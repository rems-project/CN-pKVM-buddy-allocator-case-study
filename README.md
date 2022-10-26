# CN pKVM buddy allocator case study

This repository contains a case study in C code verification using the
CN type system: the buddy allocator of the pKVM hypervisor for
Android.

The original files in the version we verified can be found in the [android-kvm repositories](https://android-kvm.googlesource.com/linux/+/39111fc40453747f8213cf9ef4337448d3c6197d/arch/arm64/kvm/hyp/nvhe/page_alloc.c).

Each file has a comment recording the original source code location in
the Linux source tree, retaining the original license/copyright
headers. Comments in the files point out where the code has been
modified (minor edits and additions).

The directory contains the license file `GPL-2.0` and the note
`Linux-syscall-note`.


## Navigation

The directory structure is as follows:

- [page_alloc.c](page_alloc.c) contains the main body of the buddy
  allocator code. The function `__hyp_attach_page` discussed in the
  paper and its annotations can be found here.

- [gfp.h](gfp.h) defines the buddy allocator API described in the
  paper.

- [memory.h](memory.h) contains a number of auxiliary definitions of
  functions and types.
  
- [defs.h](defs.h) defines resource predicates and logical functions,
  including the main invariant, `Hyp_pool`; it also declares
  uninterpreted functions used in the proof.

- [lemmas.h](lemmas.h) states lemmas.

- [coq_lemmas](coq_lemmas) is the directory for the Coq part of the verification:

  - [theories/Gen_Spec.v](coq_lemmas/theories/Gen_Spec.v) contains the
    lemma statements generated by CN,
  
  - [theories/Buddy_Aligned.v](coq_lemmas/theories/Buddy_Aligned.v)
    proofs about alignment and 'buddy' as specification concepts,

  - [theories/Pages_Aligned.v](coq_lemmas/theories/Pages_Aligned.v)
    proofs about invariants of this buddy allocator formalisation,

  - [theories/Inst_Spec.v](coq_lemmas/theories/Inst_Spec.v) the
    instantiation of the Coq module specifications in `Gen_Spec.v`.

  This Coq development has been checked with Coq 8.15.0.


- other `*.h`: these are various dependencies of the buddy allocator
  from the linux source tree.


## Relating this code to the paper text

### General

The main invariant, `Hyp_pool`, discussed in the paper text can be
found in [defs.h](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/defs.h#L257-L276)

The `Hyp_pool` predicate includes ownership of the pool and vmemmap
meta-data, and various well-formedness conditions, such as
`vmemmap_l_wf`, which captures purely logical (non-separation logic)
properties pertaining to the linked list structure of the vmemmap
entries: [defs.h](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/defs.h#L96-L129)


The file `defs.h` also contains the declaration of certain
uninterpreted functions, such as `page_size_of_order` [defs.h](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/defs.h#L5).
It it was not for the non-linear integer arithmetic, this would have a straightforward definition; since we here treat it as uninterpreted, we have to fill in gaps in the reasoning using lemmas, such as the following basic statement about `page_size_of_order`, called `lemma_page_size_of_order_inc`, which we state in [lemmas.h](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/lemmas.h#L64-L68).

### Coq export

As far as CN is concerned, this lemmas is `trusted`, but CN can export
Coq proof obligations: `Gen_Spec.v` defines a Coq module interface
capturing these proof obligations: it requires `page_size_of_order` to
be instantiated by some concrete Coq definition [Gen_Spec.v](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Gen_Spec.v#L10) and it requires a proof of `lemma_page_size_of_order_inc` (among others) [Gen_Spec.v](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Gen_Spec.v#L157-L162) .

We discharge these proof obligations in `Inst_Spec.v`: we instantiate `page_size_of_order` concretely with `CN_Lemmas.Pages_Aligned.page_size_of_order`
[Inst_Spec.v](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Inst_Spec.v#L13)
which is defined in `Pages_Aligned.v` [Pages_Aligned.v](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Pages_Aligned.v#L10-L11)
and
manually prove `lemma_page_size_of_order_inc` [Inst_spec.v](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Inst_Spec.v#L105-L111)
by reference to some lemma from [Pages_aligned.v](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Pages_Aligned.v#L76-L86) .

### Verification example in the paper: __hyp_attach_page loop body

The paper text walks through the verification of an example piece of
code, the loop body of the `__hyp_attach_page` function. This function can be found in [page_alloc.c](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/page_alloc.c#L175)
including its loop body and CN annotations
[page_alloc.c](https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/page_alloc.c#L224-L270).
