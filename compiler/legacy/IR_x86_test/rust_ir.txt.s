	.text
	.def	 @feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
.set @feat.00, 0
	.file	"rust_ir.txt"
	.def	 _ZN7example5blah117h85b611fdff56a62bE;
	.scl	2;
	.type	32;
	.endef
	.globl	_ZN7example5blah117h85b611fdff56a62bE # -- Begin function _ZN7example5blah117h85b611fdff56a62bE
	.p2align	4, 0x90
_ZN7example5blah117h85b611fdff56a62bE:  # @_ZN7example5blah117h85b611fdff56a62bE
# %bb.0:                                # %start
	movq	_ZN7example4BLOO17h346e6b828cbb67b6E(%rip), %rdx
	movl	$50, %eax
	retq
                                        # -- End function
	.def	 _ZN7example5blah217he1db0f05635a6e36E;
	.scl	2;
	.type	32;
	.endef
	.globl	_ZN7example5blah217he1db0f05635a6e36E # -- Begin function _ZN7example5blah217he1db0f05635a6e36E
	.p2align	4, 0x90
_ZN7example5blah217he1db0f05635a6e36E:  # @_ZN7example5blah217he1db0f05635a6e36E
.seh_proc _ZN7example5blah217he1db0f05635a6e36E
# %bb.0:                                # %start
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	callq	*%rcx
	movq	%rdx, %rax
	addq	$40, %rsp
	retq
	.seh_handlerdata
	.text
	.seh_endproc
                                        # -- End function
	.data
	.globl	_ZN7example4BLOO17h346e6b828cbb67b6E # @_ZN7example4BLOO17h346e6b828cbb67b6E
	.p2align	3
_ZN7example4BLOO17h346e6b828cbb67b6E:
	.asciz	"5\000\000\000\000\000\000"


