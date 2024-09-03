.text
.global test_and_set
test_and_set:
    movl $1, %eax                
    xchgl %eax, (%rdi)      
    ret                          
