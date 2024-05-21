.section ".text.init"
    .globl sort

/* Python code for reference
# p is an integer array
# n is the number of elements in p: n == len(p)
def sort(p, n):
    quicksort(p, 0, n - 1)
def quicksort(p, start, end):      # Sort elements from p[start] to p[end]
    if (start < end):
        q = partition(p, start, end)
        quicksort(p, start, q - 1)
        quicksort(p, q + 1, end)
def partition(p, start, end):      # Divide p[start:end] into two subarrays, one with all
    pivot = p[end]                 # elements smaller or equal to a pivot value (the last
    i = start                      # value of input array), and another with all elements
    for j in range(start, end):    # larger than the pivot. Returns the index of the pivot.
        if (p[j] <= pivot):
            (p[i], p[j]) = (p[j], p[i]) # swap
            i += 1
    (p[i], p[end]) = (p[end], p[i]) # swap
    return i
*/


// a0 represents starting point, a1 represents length
// new parameters: a1 - start, a2

sort:
    slli   a1, a1, 0x2     // multiply a1 by 4 to get accurate pointer
    addi   a2, a1, -4      // decrease end by 4 so that end is n-1
    add    a2, a0, a2  // address of p[end]
    mv     a1, a0    // grabs address for j

    li     t1, 52
    li     a5, 8
    li     t2, 12

quicksort:
    // if start >= end, end quicksort
    bge     a1, a2, justReturn    // pc <= ( reg[rs1]) >= reg[rs2]

    addi    sp, sp, -12
    sw      ra, 0(sp)
    sw      s1, 4(sp)     // this represents a0
    sw      s2, 8(sp)     // start

    mv      s2, a2     // stores end to be restored later
    mv      a6, a1    // grabs address for j
    mv      a7, a1        // saves i as start
// ----------------------------------------------------------------------
    // PARTITION STARTS HERE
    lw      s4, 0(a2)     // loads p[end]

    sub     t0, a2, a6 // rs1 - rs2
    bge     t1, t0, partitionSkipUnrolling // difference is less than 20

    partitionForLoopExtra:
        lw      a4, 0(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf2   // if end < p[j], then end 
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 0(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf2:
        lw      a4, 4(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf3   // if end < p[j], then end 
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 4(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf3:
        lw      a4, 8(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf4   // if end < p[j], then end 
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 8(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf4:
        lw      a4, 12(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf5   // if end < p[j], then end 
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 12(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf5:
        lw      a4, 16(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf6   // if end < p[j], then end 
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 16(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf6:
        lw      a4, 20(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf7   // if end < p[j], then end 
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 20(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf7:
        lw      a4, 24(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf8   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 24(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf8:
        lw      a4, 28(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf9   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 28(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf9:
        lw      a4, 32(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf10   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 32(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf10:
        lw      a4, 36(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf11   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 36(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf11:
        lw      a4, 40(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf12   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 40(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf12:
        lw      a4, 44(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf15   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        addi    a7, a7, 4   // i + 1
        sw      t0, 44(a6)    // puts p[i] into p[j]


    skipFirstIf15:
        lw      a4, 48(a6)     // loads p[j + 4]
        addi    a6, a6, 52    // j + 1

        blt     s4, a4, partitionForLoop   // if end < p[j], then end 
            // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        addi    a7, a7, 4   // i + 1
        sw      t0, -4(a6)    // puts p[i] into p[j]


//================= unrolling ==================================
    partitionForLoop:
        sub     t0, a2, a6 // rs1 - rs2
        blt     t1, t0, partitionForLoopExtra // difference is less than 10
        
    partitionSkipUnrolling:
        bge     t2, t0, partitionSkipTwo // difference is less than 3

    partitionForLoopExtra3:
        lw      a4, 0(a6)     // loads p[j]
         // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf32   // if end < p[j], then end 
       
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 0(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf32:
        lw      a4, 4(a6)     // loads p[j]
         // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf33   // if end < p[j], then end 
       

        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 4(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf33:
        lw      a4, 8(a6)     // loads p[j + 4]
        addi    a6, a6, 12    // j + 1

        blt     s4, a4, partitionForLoop   // if end < p[j], then end 
            // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, -4(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

        sub     t0, a2, a6 // rs1 - rs2

partitionSkipTwo:
        bge     a5, t0, partitionSkipThree // difference is less than 2

        partitionForLoopExtra2:
            lw      a4, 0(a6)     // loads p[j]
             // swaps p[i] and p[j]
            lw      t0, 0(a7)    // loads p[i]
            blt     s4, a4, skipFirstIf22   // if end < p[j], then end 
           
            sw      a4, 0(a7)    // put p[j] into p[i]
            sw      t0, 0(a6)    // puts p[i] into p[j]
            addi    a7, a7, 4   // i + 1

        skipFirstIf22:
            lw      a4, 4(a6)     // loads p[j + 4]
            addi    a6, a6, 8    // j + 1

            blt     s4, a4, partitionSkipThree   // if end < p[j], then end 
                // swaps p[i] and p[j]
            lw      t0, 0(a7)    // loads p[i]
            sw      a4, 0(a7)    // put p[j] into p[i]
            sw      t0, -4(a6)    // puts p[i] into p[j]
            addi    a7, a7, 4   // i + 1
            
    partitionSkipThree:
        lw      a4, 0(a6)     // loads p[j]
                // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, partitionForLoopSecondHalf   // if end < p[j], then end
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 0(a6)    // puts p[i] into p[j]

        addi    a7, a7, 4   // i + 1

    partitionForLoopSecondHalf:
        addi    a6, a6, 4    // j + 1
        bne     a6, a2, partitionSkipThree    // if j + 1 is equal to address of end, end the for loop

    // swap p[i] and p[end]
    lw       t0, 0(a7)   // loads p[i]
    sw       s4, 0(a7)   // puts p[end] into p[i]
    sw       t0, 0(a2)   // puts p[i] into p[end]sd
    // END OF PARTITION
// ----------------------------------------------------------------------

    mv      s1, a7      // this only stores i... without the base address pointer
    addi    a2, a7, -4      // subtrack 4 from q so that end is q-1
        // ============== QUICKSORT UNROLLED HERE ===============
quicksortNUMBER:
    // if start >= end, end quicksort
    bge     a1, a2, justReturnNUMBER    // pc <= ( reg[rs1]) >= reg[rs2]

    addi    sp, sp, -12
    sw      ra, 0(sp)
    sw      s1, 4(sp)     // this represents a0
    sw      s2, 8(sp)     // start

    mv      s2, a2     // stores end to be restored later
    mv      a6, a1    // grabs address for j
    mv      a7, a1        // saves i as start
// ----------------------------------------------------------------------
    // PARTITION STARTS HERE
    lw      s4, 0(a2)     // loads p[end]

    sub     t0, a2, a6 // rs1 - rs2
    bge     t1, t0, partitionSkipUnrollingNUMBER // difference is less than 20

    partitionForLoopExtraNUMBER:
        lw      a4, 0(a6)     // loads p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf2NUMBER   // if end < p[j], then end 
        // swaps p[i] and p[j]
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 0(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf2NUMBER:
        lw      a4, 4(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf3NUMBER   // if end < p[j], then end 

        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 4(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf3NUMBER:
        lw      a4, 8(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]

        blt     s4, a4, skipFirstIf4NUMBER   // if end < p[j], then end 

        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 8(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf4NUMBER:
        lw      a4, 12(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf5NUMBER   // if end < p[j], then end 

        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 12(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf5NUMBER:
        lw      a4, 16(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf6NUMBER   // if end < p[j], then end 

        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 16(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf6NUMBER:
        lw      a4, 20(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf7NUMBER   // if end < p[j], then end 

        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 20(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf7NUMBER:
        lw      a4, 24(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf8NUMBER   // if end < p[j], then end 

        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 24(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf8NUMBER:
        lw      a4, 28(a6)     // loads p[j]
                // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf9NUMBER   // if end < p[j], then end 

        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 28(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf9NUMBER:
        lw      a4, 32(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf10NUMBER   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 32(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf10NUMBER:
        lw      a4, 36(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf11NUMBER   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 36(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf11NUMBER:
        lw      a4, 40(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf12NUMBER   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 40(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf12NUMBER:
        lw      a4, 44(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf15NUMBER   // if end < p[j], then end 
        
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        addi    a7, a7, 4   // i + 1
        sw      t0, 44(a6)    // puts p[i] into p[j]


    skipFirstIf15NUMBER:
        lw      a4, 48(a6)     // loads p[j + 4]
        addi    a6, a6, 52    // j + 1

        blt     s4, a4, partitionForLoopNUMBER   // if end < p[j], then end 
            // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        addi    a7, a7, 4   // i + 1
        sw      t0, -4(a6)    // puts p[i] into p[j]


//================= unrolling ==================================
    partitionForLoopNUMBER:
        sub     t0, a2, a6 // rs1 - rs2
        blt     t1, t0, partitionForLoopExtraNUMBER // difference is less than 10
        
    partitionSkipUnrollingNUMBER:
        bge     t2, t0, partitionSkipTwoNUMBER // difference is less than 3

    partitionForLoopExtra3NUMBER:
        lw      a4, 0(a6)     // loads p[j]
         // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf32NUMBER   // if end < p[j], then end 
       
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 0(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf32NUMBER:
        lw      a4, 4(a6)     // loads p[j]
        // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, skipFirstIf33NUMBER   // if end < p[j], then end 
        

        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 4(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

    skipFirstIf33NUMBER:
        lw      a4, 8(a6)     // loads p[j + 4]
        addi    a6, a6, 12    // j + 1

        blt     s4, a4, partitionForLoopNUMBER   // if end < p[j], then end 
            // swaps p[i] and p[j]
        lw      t0, 0(a7)    // loads p[i]
        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, -4(a6)    // puts p[i] into p[j]
        addi    a7, a7, 4   // i + 1

        sub     t0, a2, a6 // rs1 - rs2

partitionSkipTwoNUMBER:
        bge     a5, t0, partitionSkipThreeNUMBER // difference is less than 2

        partitionForLoopExtra2NUMBER:
            lw      a4, 0(a6)     // loads p[j]
                        // swaps p[i] and p[j]
            lw      t0, 0(a7)    // loads p[i]
            blt     s4, a4, skipFirstIf22NUMBER   // if end < p[j], then end 

            sw      a4, 0(a7)    // put p[j] into p[i]
            sw      t0, 0(a6)    // puts p[i] into p[j]
            addi    a7, a7, 4   // i + 1

        skipFirstIf22NUMBER:
            lw      a4, 4(a6)     // loads p[j + 4]
            addi    a6, a6, 8    // j + 1

            blt     s4, a4, partitionSkipThreeNUMBER   // if end < p[j], then end 
                // swaps p[i] and p[j]
            lw      t0, 0(a7)    // loads p[i]
            sw      a4, 0(a7)    // put p[j] into p[i]
            sw      t0, -4(a6)    // puts p[i] into p[j]
            addi    a7, a7, 4   // i + 1

    partitionSkipThreeNUMBER:
        lw      a4, 0(a6)     // loads p[j]
        lw      t0, 0(a7)    // loads p[i]
        blt     s4, a4, partitionForLoopSecondHalfNUMBER   // if end < p[j], then end

        // swaps p[i] and p[j]

        
        sw      a4, 0(a7)    // put p[j] into p[i]
        sw      t0, 0(a6)    // puts p[i] into p[j]

        addi    a7, a7, 4   // i + 1

    partitionForLoopSecondHalfNUMBER:
        addi    a6, a6, 4    // j + 1
        bne     a6, a2, partitionSkipThreeNUMBER    // if j + 1 is equal to address of end, end the for loop

    // swap p[i] and p[end]
    lw       t0, 0(a7)   // loads p[i]
    sw       s4, 0(a7)   // puts p[end] into p[i]
    sw       t0, 0(a2)   // puts p[i] into p[end]sd
    // END OF PARTITION
// ----------------------------------------------------------------------

    mv      s1, a7      // this only stores i... without the base address pointer
    addi    a2, a7, -4      // subtrack 4 from q so that end is q-1
    jal     quicksort

    addi    a1, s1, 4       // q + 1. This is now start
    mv      a2, s2          // restores end
    jal     quicksort

    lw      ra, 0(sp)
    lw      s1, 4(sp)
    addi    sp, sp, 12
    lw      s2, -4(sp)


justReturnNUMBER:

    // ============== QUICKSORT UNROLLED HERE ===============

    addi    a1, s1, 4       // q + 1. This is now start
    mv      a2, s2          // restores end
    jal     quicksort

    lw      ra, 0(sp)
    lw      s1, 4(sp)
    addi    sp, sp, 12
    lw      s2, -4(sp)


justReturn:
ret

