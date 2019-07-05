	.text
	.def	 @feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
.set @feat.00, 0
	.file	"module_1"
	.def	 top_level;
	.scl	2;
	.type	32;
	.endef
	.globl	top_level               # -- Begin function top_level
	.p2align	4, 0x90
top_level:                              # @top_level
# %bb.0:                                # %entry
	movl	$50, %eax
	movl	$53, %edx
	retq
                                        # -- End function

