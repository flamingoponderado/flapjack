# Instruction forms emitted by the MIPS32 (Ziren) encoder; one line per fixture in
# Flapjack/Test/Mips32Encoding.lean, in the same order.
# Regenerate the expected bytes with scripts/mips32/check-encoder-fixtures.py.
addu $3, $4, $5
subu $3, $4, $5
and $3, $4, $5
or $3, $4, $5
xor $3, $4, $5
nor $3, $4, $0
slt $1, $4, $5
sltu $1, $4, $5
sll $3, $4, 7
srl $3, $4, 7
sra $3, $4, 7
rotr $3, $4, 7
sllv $3, $4, $5
srlv $3, $4, $5
srav $3, $4, $5
rotrv $3, $4, $5
jr $9
jalr $31, $1
mfhi $3
mflo $3
multu $4, $5
div $zero, $4, $5
bal 8
beq $4, $5, -16
bne $4, $5, 16
addiu $3, $4, -2
slti $1, $4, -2
sltiu $1, $4, -2
andi $3, $4, 0xfff0
ori $3, $4, 0xfff0
xori $3, $4, 0xfff0
lui $3, 0x1234
lbu $3, -4($4)
lhu $3, 6($4)
lw $3, 8($4)
sb $3, -4($4)
sh $3, 6($4)
sw $3, 8($4)
sll $0, $0, 0
