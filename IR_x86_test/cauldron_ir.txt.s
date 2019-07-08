	.text
	.def	 @feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
.set @feat.00, 0
	.file	"module_1"
	.def	 blah;
	.scl	2;
	.type	32;
	.endef
	.globl	blah                # -- Begin function blah
	.p2align	4, 0x90
blah:                               # @blah
# %bb.0:                                # %entry
	movl	$50, %eax
	movl	$53, %edx
	retq
                                        # -- End function
	.def	 blah2;
	.scl	2;
	.type	32;
	.endef
	.globl	blah2               # -- Begin function blah2
	.p2align	4, 0x90
blah2:                              # @blah2
.seh_proc blah2
# %bb.0:                                # %entry
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	callq	blah
	movq	%rdx, %rax
	addq	$40, %rsp
	retq
	.seh_handlerdata
	.text
	.seh_endproc
                                        # -- End function

