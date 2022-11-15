# CN pKVM buddy allocator case study

This repository contains a case study in C code verification using the
CN type system: the buddy allocator of the pKVM hypervisor for
Android.

The original files from the version we verified can be found in the [android-kvm repositories](https://android-kvm.googlesource.com/linux/+/39111fc40453747f8213cf9ef4337448d3c6197d/arch/arm64/kvm/hyp/nvhe/page_alloc.c).

Each file has a comment recording the original source code location in
the Linux source tree, retaining the original license/copyright
headers. Comments in the files point out where the code has been
modified (minor edits and additions).

The files are licensed under the GPL-2.0 license, except where a file's copyright header states otherwise.
The directory contains the license file `GPL-2.0` and the note
`Linux-syscall-note`.

The formalisation is by Christopher Pulte, Thomas Sewell, and Dhruv Makwana.

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
found in `defs.h`:
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/defs.h#L257-L276

This predicate includes ownership of the pool and vmemmap
meta-data, and ownership of the free pages. It also includes various purely logical (non-ownership) conditions, such as
`vmemmap_l_wf`, stating well-formedness
properties pertaining to the linked list structure of the vmemmap
entries: 
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/defs.h#L96-L129

The file `defs.h` also contains the declaration of certain
uninterpreted functions, for instance `page_size_of_order`: 
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/defs.h#L5 
If it was not for the non-linear integer arithmetic, this would have a straightforward definition, but since we here treat it as uninterpreted, we have to fill in gaps in the reasoning using lemmas, such as the following basic statement about `page_size_of_order`, called `lemma_page_size_of_order_inc`: https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/lemmas.h#L64-L68 


### Coq export

As far as CN is concerned, this lemmas is `trusted`, but CN can also export
Coq proof obligations. `Gen_Spec.v`, generated by CN for the buddy allocator, specifies the proof obligations resulting from such lemma statements about uninterpreted functions, in the form of a Coq module interface. 
This interface requires an instantiation of each uninterpreted function (including `page_size_of_order`) with some concrete Coq function: https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Gen_Spec.v#L10 
It also requires proofs of the lemma statements. For instance, the example lemma `lemma_page_size_of_order_inc` turns into the following Coq proof obligation -- which directly matches the original CN lemma statement, except that it also includes range information for `order` derived from its C-type: https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Gen_Spec.v#L157-L162 

`Inst_Spec.v` discharges these Coq proof obligations for the buddy allocator. 
For instance, we instantiate `page_size_of_order` with the concrete Coq function `CN_Lemmas.Pages_Aligned.page_size_of_order`
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Inst_Spec.v#L13
defined in `Pages_Aligned.v` as follows:
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Pages_Aligned.v#L10-L11
We then manually prove the lemma statements, including the one for `lemma_page_size_of_order_inc`
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Inst_Spec.v#L105-L111
by reference to some other lemma, proved in `Pages_Aligned.v`:
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/coq_lemmas/theories/Pages_Aligned.v#L76-L86 

### Verification example in the paper: __hyp_attach_page loop body

The paper text walks through the verification of an example part of the
code, the loop body of `__hyp_attach_page`. The `__hyp_attach_page` function can be found in `page_alloc.c`
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/page_alloc.c#L175
including its loop body and CN annotations:
https://github.com/rems-project/CN-pKVM-buddy-allocator-case-study/blob/0d028999318e85a46bb52ebcfe4afcc102e60823/page_alloc.c#L224-L270 
