	.text
	.file	"playground.e2r85j00-cgu.0"
	.globl	_ZN10playground4blah17hcf328a0bab964a12E # -- Begin function _ZN10playground4blah17hcf328a0bab964a12E
	.p2align	4, 0x90
	.type	_ZN10playground4blah17hcf328a0bab964a12E,@function
_ZN10playground4blah17hcf328a0bab964a12E: # @_ZN10playground4blah17hcf328a0bab964a12E
	.cfi_startproc
# %bb.0:                                # %start
	movl	$50, %eax
	movl	$75, %edx
	retq
.Lfunc_end0:
	.size	_ZN10playground4blah17hcf328a0bab964a12E, .Lfunc_end0-_ZN10playground4blah17hcf328a0bab964a12E
	.cfi_endproc
                                        # -- End function
	.globl	_ZN10playground5blah217hcfa468985c8317c9E # -- Begin function _ZN10playground5blah217hcfa468985c8317c9E
	.p2align	4, 0x90
	.type	_ZN10playground5blah217hcfa468985c8317c9E,@function
_ZN10playground5blah217hcfa468985c8317c9E: # @_ZN10playground5blah217hcfa468985c8317c9E
	.cfi_startproc
# %bb.0:                                # %start
	pushq	%rax
	.cfi_def_cfa_offset 16
	callq	*%rdi
	imulq	$53, %rax, %rax
	addq	%rdx, %rax
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end1:
	.size	_ZN10playground5blah217hcfa468985c8317c9E, .Lfunc_end1-_ZN10playground5blah217hcfa468985c8317c9E
	.cfi_endproc
                                        # -- End function

	.section	".note.GNU-stack","",@progbits
