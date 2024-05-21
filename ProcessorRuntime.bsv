import FIFO::*;
import FIFOF::*;
import SpecialFIFOs::*;
import Common::*;
import ProcTypes::*;
import RFile::*;
import Decode::*;
import Execute::*;
import Scoreboard::*;
// import ScheduleMonitor::*;
import Vector::*;
import BuildVector::*;
import RegFile::*;
import Ehr::*;
import SFifo::*;

typedef struct {
   Word pc;
   Word ppc;
   Bool epoch;
   } F2D deriving(Bits, Eq);

typedef struct {
   Word pc;
   Word ppc;
   Bool epoch;
   DecodedInst dInst; 
   Word rVal1; 
   Word rVal2;
   } D2E deriving(Bits, Eq);

typedef struct {
   ExecInst eInst; 
   Bool kill;
} E2W deriving(Bits, Eq);

typedef struct {
     ExecInst eInst;
   Bit#(32) pcE; 
   Bit#(32) nextPC; 
   // Bool kill;
} BpredFast deriving(Bits, Eq);

typedef struct {
   ExecInst eInst;
} E2D deriving(Bits, Eq);


typedef Bit#(32) Addr;
typedef Bit#(5) LineIdx;

interface ProcIfc;
    method Bit#(32) getPC;
endinterface

interface NextAddressPredictor;
    method Addr prediction(Addr pc);
    method Action update(Addr pc, Addr target);
endinterface

module mkBTB(NextAddressPredictor);
    Vector#(TExp#(5), Reg#(Bit#(2))) validBit <- replicateM(mkReg(0));

    RegFile#(LineIdx, Addr) tagArr <- mkRegFileFull;
    RegFile#(LineIdx, Addr) targetArr <- mkRegFileFull;

    method Addr prediction(Addr pc);
        LineIdx index = truncate(pc >> 2);
        let tag = tagArr.sub(index);
        let target = targetArr.sub(index);
        if ((tag == pc) && (validBit[index][1] == 1)) begin
            return target;
        end
        else begin
            return (pc + 4);
        end
    endmethod

    method Action update(Addr pc, Addr target);
        LineIdx index = truncate(pc >> 2);

        if ((pc + 4) == target) begin
            // tagArr.upd(index, pc);
            
            if (validBit[index] != 2'b00)
                validBit[index] <= validBit[index] - 1;
        end
        else begin
            tagArr.upd(index, pc);
            targetArr.upd(index, target);

            if (validBit[index] != 2'b11)
                validBit[index] <= validBit[index] + 1;
        end
    endmethod
endmodule

(* synthesize *)
module mkProcessor(ProcIfc);
    Reg#(Word)  pc <- mkReg(0);
    RFile2R1W   rf <- mkBypassRFile;
    Memory     iMem <- mkMemory;  //  req/res memory
    Memory     dMem <- mkMemory;  //  req/res memory
    // ScheduleMonitor monitor <- mkScheduleMonitor(stdout, vec("fetch", "decode", "execute", "writeback"));
    //Pipeline FIFOs
    FIFO#(F2D) f2d <- mkFIFO;
    FIFO#(D2E) d2e <- mkFIFO;
    FIFO#(E2W) e2w <- mkFIFO;
    FIFO#(BpredFast) bpredFast <- mkFIFO;

    FIFOF#(E2D) e2d <- mkBypassFIFOF; // e2d.notEmpty e2d.notFull

    NextAddressPredictor bpred <- mkBTB;

    Reg#(Bool)  epoch <- mkReg(False);

    Reg#(Bool)  loadWaitReg <- mkReg(False);
    // Reg#(RIndx) dstLoad <- mkReg(0); // bypass fifo enq and deq for that
    FIFO#(RIndx) dstLoad <- mkFIFO; // bypass fifo enq and deq for that

    Reg#(Word)  fetchedInst <- mkRegU;

    Reg#(Bool) hazardFlag <- mkReg(False);
    Reg#(Bool) shouldRedirect <- mkReg(False);
    Reg#(Bool) doExecuteBlock <- mkReg(True);
    Reg#(Word) redirectPC <- mkReg(0);
    
    // Instantiation of Scoreboard. 
    // An extra slot than needed is allocated to allow concurrent insert and remove when sb has n-1 items
    Scoreboard#(3)  sb <- mkBypassingScoreboard;
    
////////////////////////////////////////////////////////////////////////////////
/// WARNING: DO NOT CHANGE THIS SECTION
////////////////////////////////////////////////////////////////////////////////
    Reg#(Bit#(64)) cycles <- mkReg(0);
    Reg#(Bit#(64)) instCnt <- mkReg(0);
    rule doCycle;
        cycles <= cycles + 1;
        if ( cycles > 10000000 ) begin
            $display("FAILED: Your processor timed out");
            $finish;
        end
    endrule
////////////////////////////////////////////////////////////////////////////////
/// END OF WARNING: DO NOT CHANGE THIS SECTION
////////////////////////////////////////////////////////////////////////////////

    rule doFetch if (!shouldRedirect);
        let ppc = bpred.prediction(pc);
        iMem.req(MemReq{op: Ld, addr: pc, data: ?});
        f2d.enq(F2D {pc: pc, ppc: ppc, epoch: epoch});
        pc <= ppc;
        // monitor.record("fetch", "F");
     endrule

    rule doDecode;
////////////////////////////////////////////////////////////////////////////////
/// Student's Task : Issue 1
/// Fix the code in this rule such that no new instruction
/// should be fetched in the stalled state
////////////////////////////////////////////////////////////////////////////////
        let inst = fetchedInst;
        if (!hazardFlag) begin
            inst <- iMem.resp();
        end

        // let y = e2d.first;
        // let dst = y.dst;
        // let data = y.data;


        // let isDstValid = True;
        // if (!isValid(dst))
        //     isDstValid = False;

        let x = f2d.first;
        let epochD = x.epoch;
        if (epochD == epoch) begin  // right-path instruction
            let dInst = decode(inst); // rs1, rs2 are Maybe types
            // check for data hazard

            // Bool byPassSrc1 = False;
            Bool byPassSrc2 = False;

            Word bypassVal = 0;
            if (e2d.notEmpty) begin
                // is it same as dst
                // byPassSrc1 = (dInst.src1 == e2d.first.eInst.dst); 
                byPassSrc2 = (dInst.src2 == e2d.first.eInst.dst);
                bypassVal = e2d.first.eInst.data;                

                e2d.deq;
            end

            //Bool byPassing = (dInst.src1 == dst) || (dInst.src2 == dst);

            //let hazard = ((byPassSrc1 && sb.search1(dInst.src1))
            //             || byPassSrc2 && sb.search2(dInst.src2));

            let hazard1 = False;
            let hazard2 = False;
            // if (!byPassSrc1) begin
                if (sb.search1(dInst.src1))
                    hazard1 = True;
            // end

            if (!byPassSrc2) begin
                if (sb.search2(dInst.src2))
                    hazard2 = True;
            end

            let hazard = hazard1 || hazard2;
            // hazardFlag <= hazard;

            // if no hazard detected
            if (!hazard) begin
                hazardFlag <= False;
                let rVal1 = rf.rd1(fromMaybe(?, dInst.src1));
                let rVal2 = (byPassSrc2) ? bypassVal : rf.rd2(fromMaybe(?, dInst.src2));
                // check if bypass is available by checking source matching IDs
                // read from bypass fifo
                // otherwise read from register files directly
                // hazard condition change based on bypass availability.
                // if bypass is enabled then don't read from scoreboard, no hazard
                // watch out for 0. That's just random noise.
                sb.insert(dInst.dst); // for detecting future data hazards
                d2e.enq(D2E {pc: x.pc, ppc: x.ppc, epoch: x.epoch, 
                             dInst: dInst, rVal1: rVal1, rVal2: rVal2});
                f2d.deq;
                // monitor.record("decode", "D");
            end
            // if hazard detected
            else begin 
                fetchedInst <= inst; 
                hazardFlag <= True;
                // monitor.record("decode", "s");
            end
        end
        else begin // wrong-path instruction
            f2d.deq;
            hazardFlag <= False;
            // monitor.record("decode", "x");
        end
    endrule


    rule doExecute if ((!shouldRedirect) && (!loadWaitReg));
////////////////////////////////////////////////////////////////////////////////
/// Student's Task: Issue 2
/// Fix the code in this rule by removing item from scoreboard when
/// an instruction completes execution
////////////////////////////////////////////////////////////////////////////////

        let x = d2e.first;          
        let pcE = x.pc; let ppc = x.ppc; let epochE = x.epoch; 
        let rVal1 = x.rVal1; let rVal2 = x.rVal2; 
        let dInst = x.dInst;
        d2e.deq;

        if (epochE == epoch) begin  // right-path instruction
            let eInst = exec(dInst, rVal1, rVal2, pcE);
            instCnt <= instCnt + 1; // increment executed instructions
            if (eInst.iType == Unsupported) begin
                $display("Reached unsupported instruction");
                $display("Total Clock Cycles = %d\nTotal Instruction Count = %d", cycles, instCnt);
                $display("Dumping the state of the processor");
                $display("pc = 0x%x", x.pc);
                rf.displayRFileInSimulation;
                $display("Quitting simulation.");
                $finish;
            end


            let misprediction = eInst.nextPC != ppc;
////////////////////////////////////////////////////////////////////////////////
/// Student's Task: Issue 3
/// Modifying the following code section to fix doFetch and doExecute rule conflicts
/// by spliting doExecute rule; Don't forget modify guards of related rules
////////////////////////////////////////////////////////////////////////////////
            if ( misprediction ) begin
                // redirect the pc

                shouldRedirect <= !shouldRedirect;
                redirectPC <= eInst.nextPC;
            end
////////////////////////////////////////////////////////////////////////////////
/// End of code section for Student's Task: Issue 3
////////////////////////////////////////////////////////////////////////////////

            bpredFast.enq(BpredFast{eInst: eInst, pcE: pcE, nextPC: eInst.nextPC});
            // bpred.update(pcE, eInst.nextPC);
            
            if (eInst.iType == LOAD) begin
                dMem.req(MemReq{op: Ld, addr: eInst.addr, data: ?});
                // dstLoad <= fromMaybe(?, eInst.dst);
                dstLoad.enq(fromMaybe(?, eInst.dst));
                e2w.enq(E2W {eInst: eInst, kill: False});
                // e2d.enq(E2D {eInst: eInst});
            end 
            else if (eInst.iType == STORE) begin
////////////////////////////////////////////////////////////////////////////////
/// WARNING: The following codes should always be executed together
///          Otherwise test.sh won't work
////////////////////////////////////////////////////////////////////////////////
                if ( eInst.addr == 'h4000_1000)
                    $display("Total Clock Cycles = %d\nTotal Instruction Count = %d", cycles, instCnt);
                dMem.req(MemReq{op: St, addr: eInst.addr, 
                                data: eInst.data});
////////////////////////////////////////////////////////////////////////////////
/// END OF WARNING
////////////////////////////////////////////////////////////////////////////////
                e2w.enq(E2W {eInst: eInst, kill: False});
                // sb.remove();
                e2d.enq(E2D {eInst: eInst});
            end
            else begin
                e2w.enq(E2W {eInst: eInst, kill: False});
                e2d.enq(E2D {eInst: eInst});
            end
            // monitor.record("execute", "E");
        end
        else begin
            // sb.remove();
            //e2d.enq(E2D {eInst: ?});
            e2w.enq(E2W {eInst: ?, kill: True});
            // monitor.record("execute", "x");
        end
    endrule

    // turn dst load into bypass fifo
    // only do sb.remove() in doWrite Back

    rule bPredUpdate;
        let x = bpredFast.first;
        bpredFast.deq;

    if (x.eInst.iType == BRANCH)
        bpred.update(x.pcE, x.nextPC);
    else if (x.eInst.iType == JAL)
        bpred.update(x.pcE, x.nextPC);
    else if (x.eInst.iType == JALR)
        bpred.update(x.pcE, x.nextPC);
    endrule

    rule doWriteBack;
        let x = e2w.first;       
        let eInst = x.eInst;
        e2w.deq;

        if (e2w.first.kill == False) begin
            if(isValid(eInst.dst)) begin
                if (eInst.iType == LOAD) begin
                    let data <- dMem.resp();
                    rf.wr(dstLoad.first, data);
                    dstLoad.deq;
                end
                else if (eInst.iType != STORE) begin
                    rf.wr(fromMaybe(?, eInst.dst), eInst.data);
                end
            end
        end

        sb.remove();
        // monitor.record("writeback", "W");
    endrule

    rule doExecuteKill(shouldRedirect);
        sb.remove();
        // d2e.deq();
    endrule

    rule doExecuteKill2(shouldRedirect);
        // sb.remove();
        d2e.deq();
    endrule

    rule doRedirection if (shouldRedirect); // add guard when necessary
////////////////////////////////////////////////////////////////////////////////
/// Student's Task: Issue 3
/// Fill in this rule to fix doFetch and doExecute rule conflicts
/// by spliting doExecute rule; Don't forget modify guards of related rules
////////////////////////////////////////////////////////////////////////////////
        pc <= redirectPC + 4;
        epoch <= !epoch;
        shouldRedirect <= !shouldRedirect;
        // monitor.record("fetch", "R");
    endrule

    rule doRedirectionSplit if (shouldRedirect); // add guard when necessary
        iMem.req(MemReq{op: Ld, addr: redirectPC, data: ?});
        f2d.enq(F2D{pc:redirectPC, ppc: redirectPC + 4, epoch: !epoch});
        // monitor.record("fetch", "R");
    endrule
    
    method Bit#(32) getPC;
        return pc;
    endmethod

endmodule
