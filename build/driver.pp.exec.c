#include "cn.h"
#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

void cn_print_nr_u64(int, unsigned long);
/* originally: arch/arm64/kvm/hyp/nvhe/page_alloc.c */
// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google LLC
 * Author: Quentin Perret <qperret@google.com>
 */
/* originally ./include/uapi/asm-generic/posix_types.h */
/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
typedef unsigned long __kernel_ulong_t;
typedef __kernel_ulong_t __kernel_size_t;
/* originally ./include/linux/stddef.h */
/* SPDX-License-Identifier: GPL-2.0 */
void *copy_alloc_id(unsigned long long i, void *p);
#pragma clang diagnostic ignored "-Wunused-value"
void *copy_alloc_id(unsigned long long i, void *p) {
  /* EXECUTABLE CN PRECONDITION */
  void* __cn_ret;
  ghost_stack_depth_incr();
  cn_bits_u64* i_cn = convert_to_cn_bits_u64(i);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &i, sizeof(unsigned long long));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(void*));
  
    (unsigned long long) CN_LOAD(p);
    { __cn_ret = (void*) CN_LOAD(i); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &i, sizeof(unsigned long long));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(void*));

{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  ghost_stack_depth_decr();
}

return __cn_ret;

}
/* originally: ./tools/include/uapi/linux/const.h */
/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
/* const.h: Macros for dealing with constants.  */

/* CP: we fix a value for PAGE_SHIFT */
/* originally: ./arch/arm64/include/asm/page-def.h */
/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Based on arch/arm/include/asm/page.h
 *
 * Copyright (C) 1995-2003 Russell King
 * Copyright (C) 2017 ARM Ltd.
 */
typedef char PAGE_SIZE_t[((1UL) << 12)];
/* originally: ./include/vdso/limits.h */
/* SPDX-License-Identifier: GPL-2.0 */
/* originally: ./include/linux/mmzone.h */
/* SPDX-License-Identifier: GPL-2.0 */
/* originally: ./include/uapi/asm-generic/int-ll64.h */
/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
/*
 * asm-generic/int-ll64.h
 *
 * Integer declarations for architectures which use "long long"
 * for 64-bit types.
 */
typedef unsigned char __u8;
typedef unsigned long long __u64;
typedef signed /* __signed__ */ long long __s64;
/* originally: ./include/asm-generic/int-ll64.h */
/* SPDX-License-Identifier: GPL-2.0 */
/*
 * asm-generic/int-ll64.h
 *
 * Integer declarations for architectures which use "long long"
 * for 64-bit types.
 */
typedef __u8 u8;
typedef __u64 u64;
typedef __s64 s64;
/* originally ./include/linux/types.h */
/* SPDX-License-Identifier: GPL-2.0 */
typedef __kernel_size_t size_t;
typedef u64 phys_addr_t;
;
/* originally: ./tools/virtio/linux/kernel.h */
/* SPDX-License-Identifier: GPL-2.0 */
/* originally: */
/* #define container_of(ptr, type, member) ({            \ */
/*     const typeof( ((type *)0)->member ) *__mptr = (ptr);    \ */
/*     (type *)( (char *)__mptr - offsetof(type,member) );}) */
/* originally: ./include/linux/list.h */
/* SPDX-License-Identifier: GPL-2.0 */
static inline int list_empty(const struct list_head *head)
/*@ requires take O = Owned(head); @*/
/*@ requires ptr_eq(head, (*head).next) || !addr_eq(head, (*head).next); @*/
/*@ ensures take OR = Owned(head); @*/
/*@ ensures O == OR; @*/
/*@ ensures return == (((*head).next == head) ? 1i32 : 0i32); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* head_cn = convert_to_cn_pointer(head);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O_cn = owned_struct_list_head(head_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_or(cn_pointer_equality(head_cn, O_cn->next), cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(head_cn), cast_cn_pointer_to_cn_bits_u64(O_cn->next)))));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &head, sizeof(const struct list_head*));
  
    /* return READ_ONCE(head->next) == head; */
    { __cn_ret = CN_LOAD(CN_LOAD(head)->next) == CN_LOAD(head); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &head, sizeof(const struct list_head*));

{
  cn_bits_i32* return_cn = convert_to_cn_bits_i32(__cn_ret);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* OR_cn = owned_struct_list_head(head_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(head); @*/\n            ^~~~~~~~ ./driver.pp.c:78:13-21");
  cn_assert(struct_list_head_cn_equality(O_cn, OR_cn));
  update_cn_error_message_info("/*@ ensures O == OR; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:79:13-62");
  cn_assert(cn_bits_i32_equality(return_cn, cn_ite(cn_pointer_equality(OR_cn->next, head_cn), convert_to_cn_bits_i32(1), convert_to_cn_bits_i32(0))));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
/* renamed list to llist to avoid clash with CN keyword list */
static inline void INIT_LIST_HEAD(struct list_head *llist)
/*@ requires take O = Owned(llist); @*/
/*@ ensures take OR = Owned(llist); @*/
/*@ ensures (*llist).next == llist; (*llist).prev == llist; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* llist_cn = convert_to_cn_pointer(llist);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O_cn = owned_struct_list_head(llist_cn, GET);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &llist, sizeof(struct list_head*));
  
    /* WRITE_ONCE (llist->next, llist); */
    CN_STORE(CN_LOAD(llist)->next, CN_LOAD(llist));
    CN_STORE(CN_LOAD(llist)->prev, CN_LOAD(llist));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &llist, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  struct list_head_cn* OR_cn = owned_struct_list_head(llist_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(llist); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:88:13-36");
  cn_assert(cn_pointer_equality(OR_cn->next, llist_cn));
  update_cn_error_message_info("/*@ ensures take OR = Owned(llist); @*/\n                                    ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:88:37-60");
  cn_assert(cn_pointer_equality(OR_cn->prev, llist_cn));
  ghost_stack_depth_decr();
}
;
}
static inline _Bool __list_del_entry_valid(struct list_head *entry)
/*@ ensures return == 1u8; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  _Bool __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* entry_cn = convert_to_cn_pointer(entry);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &entry, sizeof(struct list_head*));
  
    { __cn_ret = 1; goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &entry, sizeof(struct list_head*));

{
  cn_bits_u8* return_cn = convert_to_cn_bits_u8(__cn_ret);
  update_cn_error_message_info("static inline _Bool __list_del_entry_valid(struct list_head *entry)\n            ^~~~~~~~~~~~~~ ./driver.pp.c:95:13-27");
  cn_assert(cn_bits_u8_equality(return_cn, convert_to_cn_bits_u8(1)));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
static inline void __list_del(struct list_head * prev, struct list_head * next)
/*@ requires take O1 = Owned(prev); @*/
/*@ requires take O2 = O_struct_list_head(next, prev != next); @*/
/*@ ensures take O1R = Owned(prev); @*/
/*@ ensures take O2R = O_struct_list_head(next, prev != next); @*/
/*@ ensures (prev == next) || (O2.next == O2R.next); @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged; @*/
/*@ ensures (*prev).next == next; @*/
/*@ ensures (prev == next) || (O2R.prev == prev); @*/
/*@ ensures (prev != next) || ((*prev).prev == prev); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* prev_cn = convert_to_cn_pointer(prev);
  cn_pointer* next_cn = convert_to_cn_pointer(next);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1_cn = owned_struct_list_head(prev_cn, GET);
  update_cn_error_message_info("/*@ requires take O1 = Owned(prev); @*/\n                  ^./driver.pp.c:101:19:");
  struct list_head_cn* O2_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), GET);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));
  c_add_local_to_ghost_state((uintptr_t) &next, sizeof(struct list_head*));
  
        
        CN_STORE(CN_LOAD(next)->prev, CN_LOAD(prev));
        /* WRITE_ONCE (prev->next, next); */
        CN_STORE(CN_LOAD(prev)->next, CN_LOAD(next));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));

  c_remove_local_from_ghost_state((uintptr_t) &next, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1R_cn = owned_struct_list_head(prev_cn, PUT);
  update_cn_error_message_info("/*@ ensures take O1R = Owned(prev); @*/\n                 ^./driver.pp.c:103:18:");
  struct list_head_cn* O2R_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take O2R = O_struct_list_head(next, prev != next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:104:13-53");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O2_cn->next, O2R_cn->next)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O2.next == O2R.next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:105:13-56");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O1R_cn->prev, O1_cn->prev)));
  update_cn_error_message_info("/*@ ensures (prev == next) || {(*prev).prev} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:106:13-34");
  cn_assert(cn_pointer_equality(O1R_cn->next, next_cn));
  update_cn_error_message_info("/*@ ensures (*prev).next == next; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:107:13-50");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O2R_cn->prev, prev_cn)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O2R.prev == prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:108:13-54");
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), cn_pointer_equality(O1R_cn->prev, prev_cn)));
  ghost_stack_depth_decr();
}
;
}
static inline void __list_del_entry(struct list_head *entry)
/*@ requires take O1 = Owned(entry); @*/
/*@ requires let prev = (*entry).prev; let next = (*entry).next; @*/
/*@ requires take O2 = O_struct_list_head(prev, prev != entry); @*/
/*@ requires take O3 = O_struct_list_head(next, prev != next); @*/
/*@ requires (prev != entry) || (next == entry); @*/
/*@ ensures take O1R = Owned(entry); @*/
/*@ ensures {*entry} unchanged; @*/
/*@ ensures take O2R = O_struct_list_head(prev, prev != entry); @*/
/*@ ensures take O3R = O_struct_list_head(next, prev != next); @*/
/*@ ensures (prev == next) || (O3.next == O3R.next); @*/
/*@ ensures (prev == next) || (O2.prev == O2R.prev); @*/
/*@ ensures (prev == entry) || (O2R.next == next); @*/
/*@ ensures (prev == next) || (O3R.prev == prev); @*/
/*@ ensures (prev != next) || ((prev == entry) || (O2R.prev == prev)); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* entry_cn = convert_to_cn_pointer(entry);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1_cn = owned_struct_list_head(entry_cn, GET);
  cn_pointer* prev_cn = O1_cn->prev;
  cn_pointer* next_cn = O1_cn->next;
  update_cn_error_message_info("/*@ requires let prev = (*entry).prev; let next = (*entry).next; @*/\n                  ^./driver.pp.c:118:19:");
  struct list_head_cn* O2_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_pointer_equality(prev_cn, entry_cn)), GET);
  update_cn_error_message_info("/*@ requires take O2 = O_struct_list_head(prev, prev != entry); @*/\n                  ^./driver.pp.c:119:19:");
  struct list_head_cn* O3_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, entry_cn)), cn_pointer_equality(next_cn, entry_cn)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &entry, sizeof(struct list_head*));
  
        
        
    if (!__list_del_entry_valid(CN_LOAD(entry)))
        goto __cn_epilogue;

    __list_del(CN_LOAD(CN_LOAD(entry)->prev), CN_LOAD(CN_LOAD(entry)->next));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &entry, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1R_cn = owned_struct_list_head(entry_cn, PUT);
  update_cn_error_message_info("/*@ ensures take O1R = Owned(entry); @*/\n            ^~~~~~~~~~~~~~~~~~~ ./driver.pp.c:122:13-32");
  cn_assert(struct_list_head_cn_equality(O1R_cn, O1_cn));
  update_cn_error_message_info("/*@ ensures {*entry} unchanged; @*/\n                 ^./driver.pp.c:123:18:");
  struct list_head_cn* O2R_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_pointer_equality(prev_cn, entry_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take O2R = O_struct_list_head(prev, prev != entry); @*/\n                 ^./driver.pp.c:124:18:");
  struct list_head_cn* O3R_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take O3R = O_struct_list_head(next, prev != next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:125:13-53");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3_cn->next, O3R_cn->next)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3.next == O3R.next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:126:13-53");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O2_cn->prev, O2R_cn->prev)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O2.prev == O2R.prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:127:13-51");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, entry_cn), cn_pointer_equality(O2R_cn->next, next_cn)));
  update_cn_error_message_info("/*@ ensures (prev == entry) || (O2R.next == next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:128:13-50");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3R_cn->prev, prev_cn)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3R.prev == prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:129:13-71");
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), cn_bool_or(cn_pointer_equality(prev_cn, entry_cn), cn_pointer_equality(O2R_cn->prev, prev_cn))));
  ghost_stack_depth_decr();
}
;
}
static inline void list_del_init(struct list_head *entry)
/*@ requires take O1 = Owned(entry); @*/
/*@ requires let prev = (*entry).prev; let next = (*entry).next; @*/
/*@ requires take O2 = Owned(prev); @*/
/*@ requires take O3 = O_struct_list_head(next, prev != next); @*/
/*@ requires (*entry).prev != entry; @*/
/*@ ensures take O1R = Owned(entry); @*/
/*@ ensures (*entry).prev == entry; (*entry).next == entry; @*/
/*@ ensures take O2R = Owned(prev); @*/
/*@ ensures take O3R = O_struct_list_head(next, prev != next); @*/
/*@ ensures (prev == next) || (O3.next == O3R.next); @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged; @*/
/*@ ensures (*prev).next == next; @*/
/*@ ensures (prev == next) || (O3R.prev == prev); @*/
/*@ ensures (prev != next) || ((*prev).prev == prev); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* entry_cn = convert_to_cn_pointer(entry);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1_cn = owned_struct_list_head(entry_cn, GET);
  cn_pointer* prev_cn = O1_cn->prev;
  cn_pointer* next_cn = O1_cn->next;
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O2_cn = owned_struct_list_head(prev_cn, GET);
  update_cn_error_message_info("/*@ requires take O2 = Owned(prev); @*/\n                  ^./driver.pp.c:141:19:");
  struct list_head_cn* O3_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_pointer_equality(O1_cn->prev, entry_cn)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &entry, sizeof(struct list_head*));
  
        /*CN*/ if(CN_LOAD(CN_LOAD(entry)->prev) != CN_LOAD(entry))
        ;
        /*CN*/ if(CN_LOAD(CN_LOAD(entry)->prev) != CN_LOAD(CN_LOAD(entry)->next))
        ;
    __list_del_entry(CN_LOAD(entry));
    INIT_LIST_HEAD(CN_LOAD(entry));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &entry, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1R_cn = owned_struct_list_head(entry_cn, PUT);
  update_cn_error_message_info("/*@ ensures take O1R = Owned(entry); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:144:13-36");
  cn_assert(cn_pointer_equality(O1R_cn->prev, entry_cn));
  update_cn_error_message_info("/*@ ensures take O1R = Owned(entry); @*/\n                                    ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:144:37-60");
  cn_assert(cn_pointer_equality(O1R_cn->next, entry_cn));
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O2R_cn = owned_struct_list_head(prev_cn, PUT);
  update_cn_error_message_info("/*@ ensures take O2R = Owned(prev); @*/\n                 ^./driver.pp.c:146:18:");
  struct list_head_cn* O3R_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take O3R = O_struct_list_head(next, prev != next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:147:13-53");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3_cn->next, O3R_cn->next)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3.next == O3R.next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:148:13-56");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O2R_cn->prev, O2_cn->prev)));
  update_cn_error_message_info("/*@ ensures (prev == next) || {(*prev).prev} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:149:13-34");
  cn_assert(cn_pointer_equality(O2R_cn->next, next_cn));
  update_cn_error_message_info("/*@ ensures (*prev).next == next; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:150:13-50");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3R_cn->prev, prev_cn)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3R.prev == prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:151:13-54");
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), cn_pointer_equality(O2R_cn->prev, prev_cn)));
  ghost_stack_depth_decr();
}
;
}
static inline _Bool __list_add_valid(struct list_head *new,
                struct list_head *prev,
                struct list_head *next)
/*@ ensures return == 1u8; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  _Bool __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* new_cn = convert_to_cn_pointer(new);
  cn_pointer* prev_cn = convert_to_cn_pointer(prev);
  cn_pointer* next_cn = convert_to_cn_pointer(next);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &new, sizeof(struct list_head*));
  c_add_local_to_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));
  c_add_local_to_ghost_state((uintptr_t) &next, sizeof(struct list_head*));
  
    { __cn_ret = 1; goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &new, sizeof(struct list_head*));

  c_remove_local_from_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));

  c_remove_local_from_ghost_state((uintptr_t) &next, sizeof(struct list_head*));

{
  cn_bits_u8* return_cn = convert_to_cn_bits_u8(__cn_ret);
  update_cn_error_message_info("                struct list_head *next)\n            ^~~~~~~~~~~~~~ ./driver.pp.c:163:13-27");
  cn_assert(cn_bits_u8_equality(return_cn, convert_to_cn_bits_u8(1)));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
static inline void __list_add(struct list_head *new,
                  struct list_head *prev,
                  struct list_head *next)
/*@ requires take O1 = Owned(new); take O2 = Owned(prev); take O3 = O_struct_list_head(next, prev != next); @*/
/*@ ensures take O1R = Owned(new); take O2R = Owned(prev); take O3R = O_struct_list_head(next, prev != next); @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged; @*/
/*@ ensures (prev == next) || (O3.next == O3R.next); @*/
/*@ ensures (*prev).next == new; @*/
/*@ ensures (prev == next) || (O3R.prev == new); @*/
/*@ ensures (prev != next) || ((*prev).prev == new); @*/
/*@ ensures (*new).next == next; (*new).prev == prev; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* new_cn = convert_to_cn_pointer(new);
  cn_pointer* prev_cn = convert_to_cn_pointer(prev);
  cn_pointer* next_cn = convert_to_cn_pointer(next);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1_cn = owned_struct_list_head(new_cn, GET);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O2_cn = owned_struct_list_head(prev_cn, GET);
  update_cn_error_message_info("                  struct list_head *next)\n                                                               ^./driver.pp.c:170:64:");
  struct list_head_cn* O3_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), GET);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &new, sizeof(struct list_head*));
  c_add_local_to_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));
  c_add_local_to_ghost_state((uintptr_t) &next, sizeof(struct list_head*));
  
    if (!__list_add_valid(CN_LOAD(new), CN_LOAD(prev), CN_LOAD(next)))
        goto __cn_epilogue;

        
    CN_STORE(CN_LOAD(next)->prev, CN_LOAD(new));
    CN_STORE(CN_LOAD(new)->next, CN_LOAD(next));
    CN_STORE(CN_LOAD(new)->prev, CN_LOAD(prev));
    /* WRITE_ONCE (prev->next, new); */
    CN_STORE(CN_LOAD(prev)->next, CN_LOAD(new));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &new, sizeof(struct list_head*));

  c_remove_local_from_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));

  c_remove_local_from_ghost_state((uintptr_t) &next, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1R_cn = owned_struct_list_head(new_cn, PUT);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O2R_cn = owned_struct_list_head(prev_cn, PUT);
  update_cn_error_message_info("/*@ requires take O1 = Owned(new); take O2 = Owned(prev); take O3 = O_struct_list_head(next, prev != next); @*/\n                                                                ^./driver.pp.c:171:65:");
  struct list_head_cn* O3R_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take O1R = Owned(new); take O2R = Owned(prev); take O3R = O_struct_list_head(next, prev != next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:172:13-56");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O2R_cn->prev, O2_cn->prev)));
  update_cn_error_message_info("/*@ ensures (prev == next) || {(*prev).prev} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:173:13-53");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3_cn->next, O3R_cn->next)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3.next == O3R.next); @*/\n            ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:174:13-33");
  cn_assert(cn_pointer_equality(O2R_cn->next, new_cn));
  update_cn_error_message_info("/*@ ensures (*prev).next == new; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:175:13-49");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3R_cn->prev, new_cn)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3R.prev == new); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:176:13-53");
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), cn_pointer_equality(O2R_cn->prev, new_cn)));
  update_cn_error_message_info("/*@ ensures (prev != next) || ((*prev).prev == new); @*/\n            ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:177:13-33");
  cn_assert(cn_pointer_equality(O1R_cn->next, next_cn));
  update_cn_error_message_info("/*@ ensures (prev != next) || ((*prev).prev == new); @*/\n                                 ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:177:34-54");
  cn_assert(cn_pointer_equality(O1R_cn->prev, prev_cn));
  ghost_stack_depth_decr();
}
;
}
static inline void list_add_tail(struct list_head *new, struct list_head *head)
/*@ requires take O1 = Owned(new); @*/
/*@ requires take O2 = Owned(head); @*/
/*@ requires let prev = (*head).prev; let next = head; @*/
/*@ requires take O3 = O_struct_list_head(prev, prev != next); @*/
/*@ ensures take O1R = Owned(new); take O2R = Owned(head); take O3R = O_struct_list_head(prev, prev != next); @*/
/*@ ensures (prev == next) || (O3.prev == O3R.prev); @*/
/*@ ensures (prev == next) || {(*head).next} unchanged; @*/
/*@ ensures (*head).prev == new; @*/
/*@ ensures (prev == next) || (O3R.next == new); @*/
/*@ ensures (prev != next) || ((*head).next == new); @*/
/*@ ensures (*new).next == next; (*new).prev == prev; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* new_cn = convert_to_cn_pointer(new);
  cn_pointer* head_cn = convert_to_cn_pointer(head);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1_cn = owned_struct_list_head(new_cn, GET);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O2_cn = owned_struct_list_head(head_cn, GET);
  cn_pointer* prev_cn = O2_cn->prev;
  cn_pointer* next_cn = head_cn;
  update_cn_error_message_info("/*@ requires let prev = (*head).prev; let next = head; @*/\n                  ^./driver.pp.c:192:19:");
  struct list_head_cn* O3_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), GET);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &new, sizeof(struct list_head*));
  c_add_local_to_ghost_state((uintptr_t) &head, sizeof(struct list_head*));
  
        
    __list_add(CN_LOAD(new), CN_LOAD(CN_LOAD(head)->prev), CN_LOAD(head));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &new, sizeof(struct list_head*));

  c_remove_local_from_ghost_state((uintptr_t) &head, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O1R_cn = owned_struct_list_head(new_cn, PUT);
  update_cn_error_message_info("unknown location");
  struct list_head_cn* O2R_cn = owned_struct_list_head(head_cn, PUT);
  update_cn_error_message_info("/*@ requires take O3 = O_struct_list_head(prev, prev != next); @*/\n                                                                ^./driver.pp.c:193:65:");
  struct list_head_cn* O3R_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take O1R = Owned(new); take O2R = Owned(head); take O3R = O_struct_list_head(prev, prev != next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:194:13-53");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3_cn->prev, O3R_cn->prev)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3.prev == O3R.prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:195:13-56");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O2R_cn->next, O2_cn->next)));
  update_cn_error_message_info("/*@ ensures (prev == next) || {(*head).next} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:196:13-33");
  cn_assert(cn_pointer_equality(O2R_cn->prev, new_cn));
  update_cn_error_message_info("/*@ ensures (*head).prev == new; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:197:13-49");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(O3R_cn->next, new_cn)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (O3R.next == new); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:198:13-53");
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), cn_pointer_equality(O2R_cn->next, new_cn)));
  update_cn_error_message_info("/*@ ensures (prev != next) || ((*head).next == new); @*/\n            ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:199:13-33");
  cn_assert(cn_pointer_equality(O1R_cn->next, next_cn));
  update_cn_error_message_info("/*@ ensures (prev != next) || ((*head).next == new); @*/\n                                 ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:199:34-54");
  cn_assert(cn_pointer_equality(O1R_cn->prev, prev_cn));
  ghost_stack_depth_decr();
}
;
}
/* originally: ./include/linux/minmax.h */
/* SPDX-License-Identifier: GPL-2.0 */
/* #define min(x, y)    __careful_cmp(x, y, <) */
/* originally: ./arch/arm64/kvm/hyp/include/nvhe/memory.h */
/* SPDX-License-Identifier: GPL-2.0-only */
/* #include <asm/kvm_mmu.h> */
/* #include <asm/page.h> */
/* #include <linux/types.h> */
/*
 * Accesses to struct hyp_page flags must be serialized by the host stage-2
 * page-table lock due to the lack of atomics at EL2.
 */
struct hyp_pool;
;
extern s64 hyp_physvirt_offset;
extern struct hyp_page *__hyp_vmemmap;
/*CN*/ /* extern */ void *cn_virt_base;
static inline void *hyp_phys_to_virt(phys_addr_t phys)
/*@ accesses hyp_physvirt_offset; cn_virt_base; @*/
/*@ requires let virt = phys - (u64) hyp_physvirt_offset; @*/
/*@ ensures {hyp_physvirt_offset} unchanged; @*/
/*@ ensures (u64) return == virt; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  void* __cn_ret;
  ghost_stack_depth_incr();
  cn_bits_u64* phys_cn = convert_to_cn_bits_u64(phys);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset0_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_base0_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_base)), GET);
  cn_bits_u64* virt_cn = cn_bits_u64_sub(phys_cn, cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset0_cn));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &phys, sizeof(unsigned long long));
  
    { __cn_ret = copy_alloc_id((((phys_addr_t)CN_LOAD((phys)) - CN_LOAD(hyp_physvirt_offset))), CN_LOAD((cn_virt_base))); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &phys, sizeof(unsigned long long));

{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset1_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_base1_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_base)), PUT);
  update_cn_error_message_info("/*@ requires let virt = phys - (u64) hyp_physvirt_offset; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:228:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset1_cn, O_hyp_physvirt_offset0_cn));
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:229:13-34");
  cn_assert(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(return_cn), virt_cn));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
static inline phys_addr_t hyp_virt_to_phys(void *addr)
/*@ accesses hyp_physvirt_offset; @*/
/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/
/*@ ensures {hyp_physvirt_offset} unchanged; @*/
/*@ ensures return == phys; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  unsigned long long __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* addr_cn = convert_to_cn_pointer(addr);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset2_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("/*@ accesses hyp_physvirt_offset; @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:235:25-62 (cursor: 235:35)");
  cn_bits_u64* phys_cn = cn__hyp_pa(O_hyp_physvirt_offset2_cn, addr_cn);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &addr, sizeof(void*));
  
    { __cn_ret = ((phys_addr_t)CN_LOAD((addr)) + CN_LOAD(hyp_physvirt_offset)); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &addr, sizeof(void*));

{
  cn_bits_u64* return_cn = convert_to_cn_bits_u64(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset3_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:236:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset3_cn, O_hyp_physvirt_offset2_cn));
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; @*/\n            ^~~~~~~~~~~~~~~ ./driver.pp.c:237:13-28");
  cn_assert(cn_bits_u64_equality(return_cn, phys_cn));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
enum {
  enum_PAGE_SHIFT = 12,
};

static inline u64 hyp_page_to_pfn(struct hyp_page *page)
/*@ accesses __hyp_vmemmap; @*/
/*@ requires let offs = ((u64) page) - ((u64) __hyp_vmemmap); @*/
/*@ requires offs <= max_pfn () * (sizeof<struct hyp_page>); @*/
/*@ requires mod(offs, sizeof<struct hyp_page>) == 0u64; @*/
/*@ ensures return == offs / (sizeof<struct hyp_page>); @*/
/*@ ensures {__hyp_vmemmap} unchanged; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  unsigned long long __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* page_cn = convert_to_cn_pointer(page);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap0_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  cn_bits_u64* offs_cn = cn_bits_u64_sub(cast_cn_pointer_to_cn_bits_u64(page_cn), cast_cn_pointer_to_cn_bits_u64(O___hyp_vmemmap0_cn));
  update_cn_error_message_info("/*@ requires let offs = ((u64) page) - ((u64) __hyp_vmemmap); @*/\n                     ~~~~~~~~^~ ./driver.pp.c:251:22-32 (cursor: 251:30)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(offs_cn, cn_bits_u64_multiply(max_pfn(), convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_equality(cn_bits_u64_mod(offs_cn, convert_to_cn_bits_u64(sizeof(struct hyp_page))), convert_to_cn_bits_u64(0)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &page, sizeof(struct hyp_page*));
  
  { __cn_ret = ((struct hyp_page *)CN_LOAD((page)) - ((struct hyp_page *)CN_LOAD(__hyp_vmemmap))); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &page, sizeof(struct hyp_page*));

{
  cn_bits_u64* return_cn = convert_to_cn_bits_u64(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap1_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("/*@ requires mod(offs, sizeof<struct hyp_page>) == 0u64; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:253:13-56");
  cn_assert(cn_bits_u64_equality(return_cn, cn_bits_u64_divide(offs_cn, convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
  update_cn_error_message_info("/*@ ensures return == offs / (sizeof<struct hyp_page>); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:254:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap1_cn, O___hyp_vmemmap0_cn));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
/* static inline int hyp_page_count(void *addr) */
/* { */
/*     struct hyp_page *p = hyp_virt_to_page(addr); */
/*     return p->refcount; */
/* } */
static inline int hyp_page_count(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_base; @*/
/*@ requires let hyp_vmemmap = __hyp_vmemmap; @*/
/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/
/*@ requires take H = Hyp_pool(pool, hyp_vmemmap, cn_virt_base, hyp_physvirt_offset); @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end; @*/
/*@ ensures take H2 = Hyp_pool(pool, hyp_vmemmap, cn_virt_base, hyp_physvirt_offset); @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {hyp_vmemmap} unchanged; @*/
/*@ ensures H2.pool == {H.pool}@start; @*/
/*@ ensures (u16) return == ((H2.vmemmap)[phys / (page_size())]).refcount; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* addr_cn = convert_to_cn_pointer(addr);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset4_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap2_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_base2_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_base)), GET);
  cn_pointer* hyp_vmemmap_cn = O___hyp_vmemmap2_cn;
  update_cn_error_message_info("/*@ requires let hyp_vmemmap = __hyp_vmemmap; @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:266:25-62 (cursor: 266:35)");
  cn_bits_u64* phys_cn = cn__hyp_pa(O_hyp_physvirt_offset4_cn, addr_cn);
  update_cn_error_message_info("/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/\n                  ^./driver.pp.c:267:19:");
  struct Hyp_pool_record* H_cn = Hyp_pool(pool_cn, hyp_vmemmap_cn, O_cn_virt_base2_cn, O_hyp_physvirt_offset4_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(H_cn->pool->range_start, phys_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(phys_cn, H_cn->pool->range_end));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &addr, sizeof(void*));
  
    struct hyp_page *p = (&((struct hyp_page *)CN_LOAD(__hyp_vmemmap))[((((phys_addr_t)CN_LOAD((addr)) + CN_LOAD(hyp_physvirt_offset))) >> 12)]);
c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

    /*CN*/
    /*CN*/
    /*CN*/
    /* TODO originally: return p->refcount.  Introducing 'ret' here, so we can pack resources before returning; */
    int ret = CN_LOAD(CN_LOAD(p)->refcount);
c_add_local_to_ghost_state((uintptr_t) &ret, sizeof(signed int));

        { __cn_ret = CN_LOAD(ret); 
c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &ret, sizeof(signed int));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &ret, sizeof(signed int));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &addr, sizeof(void*));

{
  cn_bits_i32* return_cn = convert_to_cn_bits_i32(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset5_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap3_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_base3_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_base)), PUT);
  update_cn_error_message_info("/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end; @*/\n                 ^./driver.pp.c:269:18:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, hyp_vmemmap_cn, O_cn_virt_base3_cn, O_hyp_physvirt_offset5_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, hyp_vmemmap, cn_virt_base, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:270:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset5_cn, O_hyp_physvirt_offset4_cn));
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, hyp_vmemmap, cn_virt_base, hyp_physvirt_offset); @*/\n                                             ^~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:270:46-70");
  cn_assert(cn_pointer_equality(hyp_vmemmap_cn, hyp_vmemmap_cn));
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; {hyp_vmemmap} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:271:13-39");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, H_cn->pool));
  update_cn_error_message_info("/*@ ensures H2.pool == {H.pool}@start; @*/\n                                                  ~~~~~~~~~^~ ./driver.pp.c:272:51-62 (cursor: 272:60)");
  update_cn_error_message_info("/*@ ensures H2.pool == {H.pool}@start; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:272:13-75");
  cn_assert(cn_bits_u16_equality(cast_cn_bits_i32_to_cn_bits_u16(return_cn), ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H2_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(cn_bits_u64_divide(phys_cn, page_size()))))->refcount));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
static inline void hyp_page_ref_inc(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount < (shift_left(1u16,16u16) - 1u16); @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == {(*p).refcount}@start + 1u16; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* O_cn = owned_struct_hyp_page(p_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_lt(O_cn->refcount, cn_bits_u16_sub(cn_bits_u16_shift_left(convert_to_cn_bits_u16(1), convert_to_cn_bits_u16(16)), convert_to_cn_bits_u16(1))));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    ((void) 0);
    CN_POSTFIX(CN_LOAD(p)->refcount, ++);

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* OR_cn = owned_struct_hyp_page(p_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(p); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:286:13-36");
  cn_assert(cn_bits_u8_equality(OR_cn->order, O_cn->order));
  update_cn_error_message_info("/*@ ensures {(*p).order} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:287:13-59");
  cn_assert(cn_bits_u16_equality(OR_cn->refcount, cn_bits_u16_add(O_cn->refcount, convert_to_cn_bits_u16(1))));
  ghost_stack_depth_decr();
}
;
}
static inline void hyp_page_ref_dec(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount > 0u16; @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == {(*p).refcount}@start - 1u16; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* O_cn = owned_struct_hyp_page(p_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_lt(convert_to_cn_bits_u16(0), O_cn->refcount));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    ((void) 0);
    CN_POSTFIX(CN_LOAD(p)->refcount, --);

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* OR_cn = owned_struct_hyp_page(p_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(p); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:296:13-36");
  cn_assert(cn_bits_u8_equality(OR_cn->order, O_cn->order));
  update_cn_error_message_info("/*@ ensures {(*p).order} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:297:13-59");
  cn_assert(cn_bits_u16_equality(OR_cn->refcount, cn_bits_u16_sub(O_cn->refcount, convert_to_cn_bits_u16(1))));
  ghost_stack_depth_decr();
}
;
}
static inline int hyp_page_ref_dec_and_test(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount > 0u16; @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == {(*p).refcount}@start - 1u16; @*/
/*@ ensures return == (((*p).refcount == 0u16) ? 1i32 : 0i32); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* O_cn = owned_struct_hyp_page(p_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_lt(convert_to_cn_bits_u16(0), O_cn->refcount));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    hyp_page_ref_dec(CN_LOAD(p));
    { __cn_ret = (CN_LOAD(CN_LOAD(p)->refcount) == 0); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  cn_bits_i32* return_cn = convert_to_cn_bits_i32(__cn_ret);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* OR_cn = owned_struct_hyp_page(p_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(p); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:306:13-36");
  cn_assert(cn_bits_u8_equality(OR_cn->order, O_cn->order));
  update_cn_error_message_info("/*@ ensures {(*p).order} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:307:13-59");
  cn_assert(cn_bits_u16_equality(OR_cn->refcount, cn_bits_u16_sub(O_cn->refcount, convert_to_cn_bits_u16(1))));
  update_cn_error_message_info("/*@ ensures (*p).refcount == {(*p).refcount}@start - 1u16; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:308:13-63");
  cn_assert(cn_bits_i32_equality(return_cn, cn_ite(cn_bits_u16_equality(OR_cn->refcount, convert_to_cn_bits_u16(0)), convert_to_cn_bits_i32(1), convert_to_cn_bits_i32(0))));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
static inline void hyp_set_page_refcounted(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount == 0u16; @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == 1u16; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* O_cn = owned_struct_hyp_page(p_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_equality(O_cn->refcount, convert_to_cn_bits_u16(0)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    ((void) 0);
    CN_STORE(CN_LOAD(p)->refcount, 1);

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* OR_cn = owned_struct_hyp_page(p_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(p); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:317:13-36");
  cn_assert(cn_bits_u8_equality(OR_cn->order, O_cn->order));
  update_cn_error_message_info("/*@ ensures {(*p).order} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:318:13-35");
  cn_assert(cn_bits_u16_equality(OR_cn->refcount, convert_to_cn_bits_u16(1)));
  ghost_stack_depth_decr();
}
;
}
/* originally: ./arch/arm64/kvm/hyp/include/nvhe/gfp.h */
/* SPDX-License-Identifier: GPL-2.0-only */
/* #include <linux/list.h> */
/* #include <nvhe/memory.h> */
/* #include <nvhe/spinlock.h> */
;
/* Allocation */
void *hyp_alloc_pages(struct hyp_pool *pool, u8 order);
// void hyp_split_page(struct hyp_page *page);
void hyp_get_page(struct hyp_pool *pool, void *addr);
void hyp_put_page(struct hyp_pool *pool, void *addr);
/* Used pages cannot be freed */
int hyp_pool_init(struct hyp_pool *pool, u64 pfn, unsigned int nr_pages,
          unsigned int reserved_pages);
// // INLINE_FUNCPTR
// extern struct hyp_pool host_s2_pool;
// struct kvm_mem_range {
//     u64 start;
//     u64 end;
// };
// struct memblock_region *find_mem_range(phys_addr_t addr, struct kvm_mem_range *range);
// bool is_in_mem_range(u64 addr, struct kvm_mem_range *range);
// bool range_is_memory(u64 start, u64 end);
//
// void *host_s2_zalloc_pages_exact(size_t size);
//
// #define _UL(x)        (_AC(x, UL))
// #define BIT(nr)            (_UL(1) << (nr))
// /* from kvm_pgtable.h */
// /**
//  * enum kvm_pgtable_prot - Page-table permissions and attributes.
//  * @KVM_PGTABLE_PROT_X:        Execute permission.
//  * @KVM_PGTABLE_PROT_W:        Write permission.
//  * @KVM_PGTABLE_PROT_R:        Read permission.
//  * @KVM_PGTABLE_PROT_DEVICE:    Device attributes.
//  * @KVM_PGTABLE_PROT_SW0:    Software bit 0.
//  * @KVM_PGTABLE_PROT_SW1:    Software bit 1.
//  * @KVM_PGTABLE_PROT_SW2:    Software bit 2.
//  * @KVM_PGTABLE_PROT_SW3:    Software bit 3.
//  */
// enum kvm_pgtable_prot {
//     KVM_PGTABLE_PROT_X            = BIT(0),
//     KVM_PGTABLE_PROT_W            = BIT(1),
//     KVM_PGTABLE_PROT_R            = BIT(2),
//
//     KVM_PGTABLE_PROT_DEVICE            = BIT(3),
//
//     KVM_PGTABLE_PROT_SW0            = BIT(55),
//     KVM_PGTABLE_PROT_SW1            = BIT(56),
//     KVM_PGTABLE_PROT_SW2            = BIT(57),
//     KVM_PGTABLE_PROT_SW3            = BIT(58),
// };
//
// bool host_stage2_force_pte_cb(u64 addr, u64 end, enum kvm_pgtable_prot prot);
// void host_s2_put_page(void *addr);
// void *host_s2_zalloc_page(void *pool);
// void host_s2_get_page(void *addr);
// // /INLINE_FUNCPTR

// define intptr_t a hacky way, for lemmas 
// /*CN*/ typedef u64 intptr_t;
/*@
lemma order_dec_inv (u64 pool_range_end, // phys_addr_t
                     u64 pfn, // u64
                     u8 order1, // unsigned int
                     u8 order2) // unsigned int
  requires order_aligned(pfn, order1);
           (pfn*page_size()) + (page_size_of_order(order1)) <= pool_range_end;
           order2 <= order1;
  ensures order_aligned(pfn, order2);
          (pfn * page_size()) + (page_size_of_order(order2)) <= pool_range_end;



lemma lemma2 (u64 p_i, // intptr_t
              u8 order) // unsigned int
  requires let p_phys = p_i * page_size();
           let buddy_i = pfn_buddy(p_i, order);
           let buddy_phys = buddy_i * page_size();
           order_aligned(p_i, order);
           order_aligned(buddy_i, order);
           p_i <= max_pfn ();
  ensures let min_i = (p_i < buddy_i) ? p_i : buddy_i;
          let min_i_phys = min_i * page_size();
          buddy_i <= max_pfn ();
          order_aligned(min_i, order+1u8);
          page_aligned(min_i_phys, order+1u8);
          (p_phys + (page_size_of_order(order)) == buddy_phys) || (p_phys - (page_size_of_order(order)) == buddy_phys);


lemma extract_l (u64 p_i, // intptr_t
                 u8 order) // unsigned int
 requires let p_phys = p_i * page_size() ;
          let buddy_i = pfn_buddy(p_i, order) ;
          let buddy_phys = buddy_i * page_size() ;
          order_aligned(p_i, order + 1u8) ;
          p_i <= max_pfn ();
 ensures p_phys + (page_size_of_order(order)) == buddy_phys ;
         page_aligned(p_phys, order) ;
         page_aligned(buddy_phys, order);


lemma page_size_of_order_inc (u8 order) // unsigned int
  requires true;
  ensures (page_size_of_order(order+1u8)) == 2u64*(page_size_of_order(order));


lemma lemma4 (u64 p_i, // intptr_t
              u8 order) // unsigned int
  requires order >= 1u8 ;
           let p_phys = p_i * page_size() ;
           order_aligned(p_i, order) ;
           p_i <= max_pfn ();
  ensures let buddy_i = pfn_buddy(p_i, order - 1u8) ;
          buddy_i <= max_pfn () ;
          let buddy_phys = buddy_i * page_size() ;
          !(order_aligned(buddy_i, order)) ;
          buddy_phys == p_phys + (page_size_of_order(order - 1u8)) ;
          0u64 < (page_size_of_order(order)) ;
          0u64 < (page_size_of_order(order - 1u8)) ;
          (page_size_of_order(order - 1u8)) * 2u64 == (page_size_of_order(order)) ;
          (page_size_of_order(order - 1u8)) <= (page_size_of_order(order)) ;
          (order_align(buddy_i, order)) == p_i;




lemma order_align_inv_loop (pointer __hypvmemmap,
                            map<u64, struct hyp_page> V,
                            struct hyp_pool pool,
                            pointer p) // struct hyp_page* 
 requires let hypvmemmap = __hypvmemmap ;
          let p_i = ((u64) p - (u64) __hypvmemmap) / 4u64 ;
          let start_i = (pool).range_start / page_size() ;
          let end_i = (pool).range_end / page_size() ;
          let p_order = (V[p_i]).order ;
          p_order >= 1u8; p_order < 11u8 ;
          order_aligned(p_i, p_order) ;
          cellPointer(hypvmemmap, 4u64, start_i, end_i, p) ;
          let buddy_i = pfn_buddy(p_i, p_order - 1u8) ;
          each(u64 i; start_i <= i && i < end_i) { page_group_ok(i, V, pool) };
 ensures buddy_i <= max_pfn () ;
         let p_new_page = {order: (p_order - 1u8), ..V[p_i]} ;
         let buddy_new_page = {order: (p_order - 1u8), ..V[buddy_i]} ;
         each(u64 i; start_i <= i && i < end_i) { page_group_ok(i, V[p_i: p_new_page, buddy_i: buddy_new_page], pool) };



lemma page_group_ok_easy (pointer __hypvmemmap, struct hyp_pool pool)
  requires let hypvmemmap = __hypvmemmap ;
           let start_i = (pool).range_start / page_size() ;
           let end_i = (pool).range_end / page_size() ;
           take V = each (u64 i; start_i <= i && i < end_i) { Owned(array_shift<struct hyp_page>(hypvmemmap, i)) } ;
           each (u64 i; start_i <= i && i < end_i) { (V[i]).order == 0u8 };
  ensures take V2 = each (u64 i; start_i <= i && i < end_i) { Owned(array_shift<struct hyp_page>(hypvmemmap, i)) } ;
          V2 == V ;
          each(u64 i; start_i <= i && i < end_i) { page_group_ok(i, V2, pool) };


lemma order_aligned_init (u64 i) // unsigned long
  requires true;
  ensures order_aligned(i, 0u8);

lemma page_size_of_order ()
  requires true;
  ensures (page_size_of_order(0u8)) == page_size();


lemma attach_inc_loop (map<u64, struct hyp_page> V,
                            pointer __hypvmemmap,
                            struct hyp_pool pool,
                            pointer p, // struct hyp_page*
                            u8 order) // unsigned int
 requires let hypvmemmap = __hypvmemmap ;
          let start_i = (pool).range_start / page_size() ;
          let end_i = (pool).range_end / page_size() ;
          cellPointer(hypvmemmap, 4u64, start_i, end_i, p) ;
          let p_i = ((u64) p - (u64) __hypvmemmap) / 4u64 ;
          let buddy_i = pfn_buddy(p_i, order) ;
          let buddy_order = (V[buddy_i]).order ;
          start_i <= buddy_i; buddy_i < end_i ;
          order + 1u8 < 11u8; buddy_order == order ;
          order_aligned(p_i, order) ;
          order_aligned(buddy_i, order) ;
          (V[p_i]).order == (hyp_no_order ()) ;
          let p_page_tweaked = {order: order, ..V[p_i]} ;
          each(u64 i; start_i <= i && i < end_i) { page_group_ok(i, V[p_i: p_page_tweaked], pool) } ;
          let min_i = (p_i < buddy_i) ? p_i : buddy_i ;
          let min_page = {order: (order + 1u8), ..V[min_i]} ;
          let buddy_page = {order: (hyp_no_order ()), ..V[buddy_i]};
 ensures each(u64 i; start_i <= i && i < end_i) { page_group_ok(i, V[buddy_i: buddy_page,min_i: min_page], pool) };




// TODO: is this (and other) lemma even useful anymore?
lemma find_buddy_xor(u64 addr_i, // intptr_t
                     u8 order) // unsigned int
  requires order_aligned(addr_i, order) ;
           order < 11u8;
  ensures let two_to_order = power_uf(2u64, (u64) order);
          0u64 < two_to_order ;
          two_to_order < shift_left(1u64, 11u64) ;
          let buddy_addr = calc_buddy(addr_i * page_size(), order) ;
          let buddy_i = (buddy_addr / page_size()) ;
          buddy_i == (pfn_buddy (addr_i, order)) ;
          (mod(buddy_addr, page_size())) == 0u64 ;
          order_aligned(buddy_i, order) ;
          addr_i != buddy_i;


lemma page_size_of_order2(u8 order) // unsigned int
  requires order < 11u8;
  ensures 0u64 < power_uf(2u64, (u64) order) ;
          power_uf(2u64, (u64) order) < shift_left(1u64, 11u64) ;
          let size = page_size() * power_uf(2u64, (u64) order) ;
          size == (page_size_of_order(order));


lemma struct_list_head_to_bytes(pointer node) // struct list_head * 
  requires take Node = Owned<struct list_head>(node);
  ensures take B = each (u64 i; ((u64) node) <= i && i < (((u64) node) + (sizeof<struct list_head>))){Byte(array_shift<char>(NULL, i))};


lemma bytes_to_struct_list_head(pointer node, // struct list_head *
                                u8 order)
  requires let length = page_size_of_order(order) ;
           let nodeI = ((u64) node) ;
           take B = each (u64 i; (nodeI <= i) && (i < (nodeI + length))) {ByteV(array_shift<char>(NULL, i), 0u8)};
  ensures take Node = Owned<struct list_head>(node) ;
          take BR = each (u64 i; (nodeI + (sizeof<struct list_head>)) <= i && i < (nodeI + length)){ByteV(array_shift<char>(NULL, i), 0u8)};

@*/
/* NOTE: we give memset a bogus empty body to overcome a limitation of
   the current CN frontend (function declarations without body loose
   the variable name information that we rely on in the
   specifications).) */
void *memset(void *b, int cc, unsigned long len);
/*@ spec memset(pointer b, i32 cc, u64 len);
    requires let b_i = (u64) b;
             let c = (u8) cc;
             take B = each (u64 i; b_i <= i && i < b_i+len){Byte(array_shift<char>(NULL, i))};
    ensures take BR = each (u64 i; b_i <= i && i < b_i+len){ByteV(array_shift<char>(NULL,i), c)}; @*/
struct hyp_page *__hyp_vmemmap;
/*CN*/
void *cn_virt_ptr;
/*
 * Index the hyp_vmemmap to find a potential buddy page, but make no assumption
 * about its current state.
 *
 * Example buddy-tree for a 4-pages physically contiguous pool:
 *
 *                 o : Page 3
 *                /
 *               o-o : Page 2
 *              /
 *             /   o : Page 1
 *            /   /
 *           o---o-o : Page 0
 *    Order  2   1 0
 *
 * Example of requests on this pool:
 *   __find_buddy_nocheck(pool, page 0, order 0) => page 1
 *   __find_buddy_nocheck(pool, page 0, order 1) => page 2
 *   __find_buddy_nocheck(pool, page 1, order 0) => page 0
 *   __find_buddy_nocheck(pool, page 2, order 0) => page 3
 */
static struct hyp_page *__find_buddy_nocheck(struct hyp_pool *pool,
                         struct hyp_page *p,
                         u8 order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; @*/
/*@ requires take O = Owned(pool); @*/
/*@ requires hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/
/*@ requires let start_i = (*pool).range_start / page_size (); @*/
/*@ requires let end_i = (*pool).range_end / page_size (); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires order_aligned(p_i, order); @*/
/*@ requires order < (*pool).max_order; @*/
/*@ ensures take OR = Owned(pool); @*/
/*@ ensures hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/
/*@ ensures {*pool} unchanged; @*/
/*@ ensures let buddy_i = pfn_buddy(p_i, order); @*/
/*@ ensures let buddy = array_shift<struct hyp_page>(__hyp_vmemmap, buddy_i); @*/
/*@ ensures let in_range_buddy = buddy_i >= start_i && buddy_i < end_i; @*/
/*@ ensures let good_buddy = in_range_buddy; @*/
/*@ ensures return == (good_buddy ? buddy : NULL); @*/
/*@ ensures is_null(return) ||
  (!addr_eq(return, NULL) && cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  struct hyp_page* __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  cn_bits_u8* order_cn = convert_to_cn_bits_u8(order);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset18_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap16_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* O_cn = owned_struct_hyp_pool(pool_cn, GET);
  update_cn_error_message_info("/*@ requires take O = Owned(pool); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1090:14-74 (cursor: 1090:25)");
  update_cn_error_message_info(NULL);
  cn_assert(hyp_pool_wf(pool_cn, O_cn, O___hyp_vmemmap16_cn, O_hyp_physvirt_offset18_cn));
  update_cn_error_message_info("/*@ requires hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/\n                                                 ~~~~~~~~~~^~ ./driver.pp.c:1091:50-62 (cursor: 1091:60)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(O_cn->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = (*pool).range_start / page_size (); @*/\n                                             ~~~~~~~~~~^~ ./driver.pp.c:1092:46-58 (cursor: 1092:56)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(O_cn->range_end, page_size());
  update_cn_error_message_info("/*@ requires let end_i = (*pool).range_end / page_size (); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1093:14-92 (cursor: 1093:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap16_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_cn));
  update_cn_error_message_info("/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1094:24-60 (cursor: 1094:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap16_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n             ~~~~~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:1095:14-39 (cursor: 1095:27)");
  update_cn_error_message_info(NULL);
  cn_assert(order_aligned(p_i_cn, order_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u8_lt(order_cn, O_cn->max_order));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  c_add_local_to_ghost_state((uintptr_t) &order, sizeof(unsigned char));
  
    phys_addr_t addr = ((phys_addr_t)(((hyp_page_to_pfn(CN_LOAD(p)))) << 12));
c_add_local_to_ghost_state((uintptr_t) &addr, sizeof(unsigned long long));

    /*CN*/
    
    CN_STORE_OP(addr,^,(((1UL) << 12) << CN_LOAD(order)));
    cn_bits_u64* read_addr0 = convert_to_cn_bits_u64(cn_pointer_deref(convert_to_cn_pointer((&addr)), unsigned long long));

cn_pointer* read___hyp_vmemmap61 = convert_to_cn_pointer(cn_pointer_deref(convert_to_cn_pointer((&__hyp_vmemmap)), struct hyp_page*));

cn_pointer* read_p40 = convert_to_cn_pointer(cn_pointer_deref(convert_to_cn_pointer((&p)), struct hyp_page*));

cn_bits_u8* read_order8 = convert_to_cn_bits_u8(cn_pointer_deref(convert_to_cn_pointer((&order)), unsigned char));

update_cn_error_message_info("    addr ^= (((1UL) << 12) << order);\n                                   ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~ ./driver.pp.c:1113:36-71 (cursor: 1113:54)");

update_cn_error_message_info("    addr ^= (((1UL) << 12) << order);\n                                                                         ~~~~~~~~~^~ ./driver.pp.c:1113:74-85 (cursor: 1113:83)");

update_cn_error_message_info("    addr ^= (((1UL) << 12) << order);\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1113:25-93 (cursor: 1113:35)");

update_cn_error_message_info(NULL);

cn_assert(cn_bits_u64_equality(read_addr0, calc_buddy(cn_bits_u64_multiply(cn_hyp_page_to_pfn(read___hyp_vmemmap61, read_p40), page_size()), read_order8)));

    /*
     * Don't return a page outside the pool range -- it belongs to
     * something else and may not be mapped in hyp_vmemmap.
     */
    if (CN_LOAD(addr) < CN_LOAD(CN_LOAD(pool)->range_start) || CN_LOAD(addr) >= CN_LOAD(CN_LOAD(pool)->range_end))
        { __cn_ret = ((void *)0); 
c_remove_local_from_ghost_state((uintptr_t) &addr, sizeof(unsigned long long));
goto __cn_epilogue; }
    { __cn_ret = (&((struct hyp_page *)CN_LOAD(__hyp_vmemmap))[(CN_LOAD((addr)) >> 12)]); 
c_remove_local_from_ghost_state((uintptr_t) &addr, sizeof(unsigned long long));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &addr, sizeof(unsigned long long));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

  c_remove_local_from_ghost_state((uintptr_t) &order, sizeof(unsigned char));

{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset19_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap17_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* OR_cn = owned_struct_hyp_pool(pool_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(pool); @*/\n            ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1098:13-73 (cursor: 1098:24)");
  update_cn_error_message_info("/*@ ensures take OR = Owned(pool); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1098:13-74");
  cn_assert(hyp_pool_wf(pool_cn, OR_cn, O___hyp_vmemmap17_cn, O_hyp_physvirt_offset19_cn));
  update_cn_error_message_info("/*@ ensures hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1099:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset19_cn, O_hyp_physvirt_offset18_cn));
  update_cn_error_message_info("/*@ ensures hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/\n                                             ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1099:46-72");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap17_cn, O___hyp_vmemmap16_cn));
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1100:13-31");
  cn_assert(struct_hyp_pool_cn_equality(OR_cn, O_cn));
  update_cn_error_message_info("/*@ ensures {*pool} unchanged; @*/\n                          ~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:1101:27-48 (cursor: 1101:36)");
  cn_bits_u64* buddy_i_cn = pfn_buddy(p_i_cn, order_cn);
  cn_pointer* buddy_cn = cn_array_shift(O___hyp_vmemmap17_cn, sizeof(struct hyp_page), buddy_i_cn);
  cn_bool* in_range_buddy_cn = cn_bool_and(cn_bits_u64_le(start_i_cn, buddy_i_cn), cn_bits_u64_lt(buddy_i_cn, end_i_cn));
  cn_bool* good_buddy_cn = in_range_buddy_cn;
  update_cn_error_message_info("/*@ ensures let good_buddy = in_range_buddy; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1105:13-51");
  cn_assert(cn_pointer_equality(return_cn, cn_ite(good_buddy_cn, buddy_cn, convert_to_cn_pointer(NULL))));
  update_cn_error_message_info("/*@ ensures is_null(return) ||\n                             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1107:30-112 (cursor: 1107:41)");
  update_cn_error_message_info("/*@ ensures is_null(return) ||\n                                                                                                                   ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~ ./driver.pp.c:1107:116-145 (cursor: 1107:129)");
  update_cn_error_message_info("/*@ ensures return == (good_buddy ? buddy : NULL); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1106:13-1107:161");
  cn_assert(cn_bool_or(cn_pointer_equality(return_cn, convert_to_cn_pointer(NULL)), cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(return_cn), cast_cn_pointer_to_cn_bits_u64(convert_to_cn_pointer(NULL)))), cellPointer(O___hyp_vmemmap17_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, buddy_cn)), order_aligned(buddy_i_cn, order_cn)), cn_bool_not(cn_pointer_equality(p_cn, buddy_cn)))));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
/* Find a buddy page currently available for allocation */
static struct hyp_page *__find_buddy_avail(struct hyp_pool *pool,
                       struct hyp_page *p,
                       u8 order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; @*/
/*@ requires take O1 = Owned(pool); @*/
/*@ requires hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/
/*@ requires let start_i = (*pool).range_start / page_size(); @*/
/*@ requires let end_i = (*pool).range_end / page_size(); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires order_aligned(p_i, order); @*/
/*@ requires order < (*pool).max_order; @*/
/*@ requires take V = each (u64 i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; @*/
/*@ ensures take OR = Owned(pool); @*/
/*@ ensures hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/
/*@ ensures take V2 = each (u64 i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; @*/
/*@ ensures V2 == V; @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/
/*@ ensures {*pool} unchanged; @*/
/*@ ensures let buddy_i = pfn_buddy(p_i, order); @*/
/*@ ensures let same_order = V2[buddy_i].order == order; @*/
/*@ ensures let zero_refcount = V2[buddy_i].refcount == 0u16; @*/
/*@ ensures let buddy = array_shift<struct hyp_page>(__hyp_vmemmap, buddy_i); @*/
/*@ ensures let in_range_buddy = buddy_i >= start_i && buddy_i < end_i; @*/
/*@ ensures let good_buddy = in_range_buddy && same_order && zero_refcount; @*/
/*@ ensures return == (good_buddy ? buddy : NULL); @*/
/*@ ensures is_null(return) || !addr_eq(return, NULL) && (cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  struct hyp_page* __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  cn_bits_u8* order_cn = convert_to_cn_bits_u8(order);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset20_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap18_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* O1_cn = owned_struct_hyp_pool(pool_cn, GET);
  update_cn_error_message_info("/*@ requires take O1 = Owned(pool); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1128:14-74 (cursor: 1128:25)");
  update_cn_error_message_info(NULL);
  cn_assert(hyp_pool_wf(pool_cn, O1_cn, O___hyp_vmemmap18_cn, O_hyp_physvirt_offset20_cn));
  update_cn_error_message_info("/*@ requires hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); @*/\n                                                 ~~~~~~~~~^~ ./driver.pp.c:1129:50-61 (cursor: 1129:59)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(O1_cn->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = (*pool).range_start / page_size(); @*/\n                                             ~~~~~~~~~^~ ./driver.pp.c:1130:46-57 (cursor: 1130:55)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(O1_cn->range_end, page_size());
  update_cn_error_message_info("/*@ requires let end_i = (*pool).range_end / page_size(); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1131:14-92 (cursor: 1131:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap18_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_cn));
  update_cn_error_message_info("/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1132:24-60 (cursor: 1132:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap18_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n             ~~~~~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:1133:14-39 (cursor: 1133:27)");
  update_cn_error_message_info(NULL);
  cn_assert(order_aligned(p_i_cn, order_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u8_lt(order_cn, O1_cn->max_order));
  update_cn_error_message_info("unknown location");
  cn_map* V_cn = map_create();
  {
  cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i_cn);
  while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i_cn, i), cn_bits_u64_lt(i, end_i_cn)))) {
    if (convert_from_cn_bool(convert_to_cn_bool(true))) {
      cn_pointer* a_8612 = cn_pointer_add_cn_bits_u64(O___hyp_vmemmap18_cn, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
      cn_map_set(V_cn, cast_cn_bits_u64_to_cn_integer(i), owned_struct_hyp_page(a_8612, GET));
    }
    else {
      ;
    }
    cn_bits_u64_increment(i);
  }
}
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  c_add_local_to_ghost_state((uintptr_t) &order, sizeof(unsigned char));
  
    struct hyp_page *buddy = __find_buddy_nocheck(CN_LOAD(pool), CN_LOAD(p), CN_LOAD(order));
c_add_local_to_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));

    /*CN*/ 
    /*CN*/ 
    if (!CN_LOAD(buddy) || CN_LOAD(CN_LOAD(buddy)->order) != CN_LOAD(order) || CN_LOAD(CN_LOAD(buddy)->refcount))
        { __cn_ret = ((void *)0); 
c_remove_local_from_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));
goto __cn_epilogue; }
    { __cn_ret = CN_LOAD(buddy); 
c_remove_local_from_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

  c_remove_local_from_ghost_state((uintptr_t) &order, sizeof(unsigned char));

{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset21_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap19_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* OR_cn = owned_struct_hyp_pool(pool_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OR = Owned(pool); @*/\n            ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1137:13-73 (cursor: 1137:24)");
  update_cn_error_message_info("/*@ ensures take OR = Owned(pool); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1137:13-74");
  cn_assert(hyp_pool_wf(pool_cn, OR_cn, O___hyp_vmemmap19_cn, O_hyp_physvirt_offset21_cn));
  update_cn_error_message_info("unknown location");
  cn_map* V2_cn = map_create();
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i_cn);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i_cn, i), cn_bits_u64_lt(i, end_i_cn)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        cn_pointer* a_8707 = cn_pointer_add_cn_bits_u64(O___hyp_vmemmap19_cn, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
        cn_map_set(V2_cn, cast_cn_bits_u64_to_cn_integer(i), owned_struct_hyp_page(a_8707, PUT));
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info("/*@ ensures take V2 = each (u64 i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; @*/\n            ^~~~~~~~ ./driver.pp.c:1139:13-21");
  cn_assert(cn_map_equality(V2_cn, V_cn, struct_hyp_page_cn_equality));
  update_cn_error_message_info("/*@ ensures V2 == V; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1140:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset21_cn, O_hyp_physvirt_offset20_cn));
  update_cn_error_message_info("/*@ ensures V2 == V; @*/\n                                             ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1140:46-72");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap19_cn, O___hyp_vmemmap18_cn));
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1141:13-31");
  cn_assert(struct_hyp_pool_cn_equality(OR_cn, O1_cn));
  update_cn_error_message_info("/*@ ensures {*pool} unchanged; @*/\n                          ~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:1142:27-48 (cursor: 1142:36)");
  cn_bits_u64* buddy_i_cn = pfn_buddy(p_i_cn, order_cn);
  cn_bool* same_order_cn = cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V2_cn, cast_cn_bits_u64_to_cn_integer(buddy_i_cn)))->order, order_cn);
  cn_bool* zero_refcount_cn = cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V2_cn, cast_cn_bits_u64_to_cn_integer(buddy_i_cn)))->refcount, convert_to_cn_bits_u16(0));
  cn_pointer* buddy_cn = cn_array_shift(O___hyp_vmemmap19_cn, sizeof(struct hyp_page), buddy_i_cn);
  cn_bool* in_range_buddy_cn = cn_bool_and(cn_bits_u64_le(start_i_cn, buddy_i_cn), cn_bits_u64_lt(buddy_i_cn, end_i_cn));
  cn_bool* good_buddy_cn = cn_bool_and(cn_bool_and(in_range_buddy_cn, same_order_cn), zero_refcount_cn);
  update_cn_error_message_info("/*@ ensures let good_buddy = in_range_buddy && same_order && zero_refcount; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1148:13-51");
  cn_assert(cn_pointer_equality(return_cn, cn_ite(good_buddy_cn, buddy_cn, convert_to_cn_pointer(NULL))));
  update_cn_error_message_info("/*@ ensures return == (good_buddy ? buddy : NULL); @*/\n                                                          ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1149:59-141 (cursor: 1149:70)");
  update_cn_error_message_info("/*@ ensures return == (good_buddy ? buddy : NULL); @*/\n                                                                                                                                                ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~ ./driver.pp.c:1149:145-174 (cursor: 1149:158)");
  update_cn_error_message_info("/*@ ensures return == (good_buddy ? buddy : NULL); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1149:13-190");
  cn_assert(cn_bool_or(cn_pointer_equality(return_cn, convert_to_cn_pointer(NULL)), cn_bool_and(cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(return_cn), cast_cn_pointer_to_cn_bits_u64(convert_to_cn_pointer(NULL)))), cn_bool_and(cn_bool_and(cellPointer(O___hyp_vmemmap19_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, buddy_cn), order_aligned(buddy_i_cn, order_cn)), cn_bool_not(cn_pointer_equality(p_cn, buddy_cn))))));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
/*
 * Pages that are available for allocation are tracked in free-lists, so we use
 * the pages themselves to store the list nodes to avoid wasting space. As the
 * allocator always returns zeroed pages (which are zeroed on the hyp_put_page()
 * path to optimize allocation speed), we also need to clean-up the list node in
 * each page when we take it out of the list.
 */
static inline void page_remove_from_list(struct hyp_page *p)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires p_i <= max_pfn (); @*/
/*@ requires let phys = p_i * page_size(); @*/
/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/
/*@ requires take OP = Owned(p); @*/
/*@ requires let order = (*p).order; @*/
/*@ requires order < 11u8; @*/
/*@ requires take AP = AllocatorPage(virt, true, order); @*/
/*@ requires let prev = AP.prev; let next = AP.next; @*/
/*@ requires take Node_prev = O_struct_list_head(prev, prev != virt); @*/
/*@ requires take Node_next = O_struct_list_head(next, prev != next); @*/
/*@ requires (prev != virt) || (next == virt); @*/
/*@ requires 0i64 <= hyp_physvirt_offset; @*/
/*@ requires (u64) hyp_physvirt_offset <= phys; phys < shift_left(1u64, 63u64); @*/
/*@ requires (mod((u64) hyp_physvirt_offset, page_size())) == 0u64; @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {cn_virt_ptr} unchanged; @*/
/*@ ensures take OP2 = Owned(p); @*/
/*@ ensures {*p} unchanged; @*/
/*@ ensures take ZP = ZeroPage(virt, true, (*p).order); @*/
/*@ ensures take Node_prev2 = O_struct_list_head(prev, prev != virt); @*/
/*@ ensures take Node_next2 = O_struct_list_head(next, prev != next); @*/
/*@ ensures (prev == next) || (Node_next2.next == Node_next.next); @*/
/*@ ensures (prev == next) || (Node_prev2.prev == Node_prev.prev); @*/
/*@ ensures (prev == virt) || (Node_prev2.next == next); @*/
/*@ ensures (prev == next) || (Node_next2.prev == prev); @*/
/*@ ensures (prev != next) || ((prev == virt) || (Node_prev2.prev == prev)); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap20_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset22_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr12_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info("/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1167:24-60 (cursor: 1167:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap20_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n                    ~~~~~~~~^~ ./driver.pp.c:1168:21-31 (cursor: 1168:29)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(p_i_cn, max_pfn()));
  update_cn_error_message_info("/*@ requires p_i <= max_pfn (); @*/\n                              ~~~~~~~~~^~ ./driver.pp.c:1169:31-42 (cursor: 1169:40)");
  cn_bits_u64* phys_cn = cn_bits_u64_multiply(p_i_cn, page_size());
  update_cn_error_message_info("/*@ requires let phys = p_i * page_size(); @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1170:25-75 (cursor: 1170:35)");
  cn_pointer* virt_cn = cn__hyp_va(O_cn_virt_ptr12_cn, O_hyp_physvirt_offset22_cn, phys_cn);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* OP_cn = owned_struct_hyp_page(p_cn, GET);
  cn_bits_u8* order_cn = OP_cn->order;
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u8_lt(order_cn, convert_to_cn_bits_u8(11)));
  update_cn_error_message_info("/*@ requires order < 11u8; @*/\n                  ^./driver.pp.c:1174:19:");
  struct list_head_cn* AP_cn = AllocatorPage(virt_cn, convert_to_cn_bool(true), order_cn, GET);
  cn_pointer* prev_cn = AP_cn->prev;
  cn_pointer* next_cn = AP_cn->next;
  update_cn_error_message_info("/*@ requires let prev = AP.prev; let next = AP.next; @*/\n                  ^./driver.pp.c:1176:19:");
  struct list_head_cn* Node_prev_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_pointer_equality(prev_cn, virt_cn)), GET);
  update_cn_error_message_info("/*@ requires take Node_prev = O_struct_list_head(prev, prev != virt); @*/\n                  ^./driver.pp.c:1177:19:");
  struct list_head_cn* Node_next_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, virt_cn)), cn_pointer_equality(next_cn, virt_cn)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_i64_le(convert_to_cn_bits_i64(0), O_hyp_physvirt_offset22_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset22_cn), phys_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(phys_cn, cn_bits_u64_shift_left(convert_to_cn_bits_u64(1), convert_to_cn_bits_u64(63))));
  update_cn_error_message_info("/*@ requires (u64) hyp_physvirt_offset <= phys; phys < shift_left(1u64, 63u64); @*/\n                                             ~~~~~~~~~^~ ./driver.pp.c:1181:46-57 (cursor: 1181:55)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_equality(cn_bits_u64_mod(cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset22_cn), page_size()), convert_to_cn_bits_u64(0)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    struct list_head *node = copy_alloc_id((((phys_addr_t)(((phys_addr_t)(((hyp_page_to_pfn(CN_LOAD(p)))) << 12))) - CN_LOAD(hyp_physvirt_offset))), CN_LOAD((cn_virt_ptr)));
c_add_local_to_ghost_state((uintptr_t) &node, sizeof(struct list_head*));

    
    
    __list_del_entry(CN_LOAD(node));
    /*CN*/
    memset(CN_LOAD(node), 0, sizeof(*node));
    /*CN*/

c_remove_local_from_ghost_state((uintptr_t) &node, sizeof(struct list_head*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap21_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset23_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr13_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires (mod((u64) hyp_physvirt_offset, page_size())) == 0u64; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1182:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap21_cn, O___hyp_vmemmap20_cn));
  update_cn_error_message_info("/*@ requires (mod((u64) hyp_physvirt_offset, page_size())) == 0u64; @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1182:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset23_cn, O_hyp_physvirt_offset22_cn));
  update_cn_error_message_info("/*@ requires (mod((u64) hyp_physvirt_offset, page_size())) == 0u64; @*/\n                                                                        ^~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1182:73-97");
  cn_assert(cn_pointer_equality(O_cn_virt_ptr13_cn, O_cn_virt_ptr12_cn));
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* OP2_cn = owned_struct_hyp_page(p_cn, PUT);
  update_cn_error_message_info("/*@ ensures take OP2 = Owned(p); @*/\n            ^~~~~~~~~~~~~~~ ./driver.pp.c:1184:13-28");
  cn_assert(struct_hyp_page_cn_equality(OP2_cn, OP_cn));
  update_cn_error_message_info("/*@ ensures {*p} unchanged; @*/\n                 ^./driver.pp.c:1185:18:");
  ZeroPage(virt_cn, convert_to_cn_bool(true), OP2_cn->order, PUT);
  update_cn_error_message_info("/*@ ensures take ZP = ZeroPage(virt, true, (*p).order); @*/\n                 ^./driver.pp.c:1186:18:");
  struct list_head_cn* Node_prev2_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_pointer_equality(prev_cn, virt_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take Node_prev2 = O_struct_list_head(prev, prev != virt); @*/\n                 ^./driver.pp.c:1187:18:");
  struct list_head_cn* Node_next2_cn = O_struct_list_head(next_cn, cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), PUT);
  update_cn_error_message_info("/*@ ensures take Node_next2 = O_struct_list_head(next, prev != next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1188:13-67");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(Node_next2_cn->next, Node_next_cn->next)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (Node_next2.next == Node_next.next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1189:13-67");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(Node_prev2_cn->prev, Node_prev_cn->prev)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (Node_prev2.prev == Node_prev.prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1190:13-57");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, virt_cn), cn_pointer_equality(Node_prev2_cn->next, next_cn)));
  update_cn_error_message_info("/*@ ensures (prev == virt) || (Node_prev2.next == next); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1191:13-57");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(Node_next2_cn->prev, prev_cn)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (Node_next2.prev == prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1192:13-77");
  cn_assert(cn_bool_or(cn_bool_not(cn_pointer_equality(prev_cn, next_cn)), cn_bool_or(cn_pointer_equality(prev_cn, virt_cn), cn_pointer_equality(Node_prev2_cn->prev, prev_cn))));
  ghost_stack_depth_decr();
}
;
}
/* for verification */
static inline void page_remove_from_list_pool(struct hyp_pool *pool, struct hyp_page *p)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires take HP = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires let phys = p_i * page_size(); @*/
/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/
/*@ requires let start_i = HP.pool.range_start / page_size(); @*/
/*@ requires let end_i = HP.pool.range_end / page_size(); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/
/*@ requires let order = HP.vmemmap[p_i].order; @*/
/*@ requires order != hyp_no_order (); @*/
/*@ requires HP.vmemmap[p_i].refcount == 0u16; @*/
/*@ ensures take ZP = ZeroPage(virt, true, order); @*/
/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
/*@ ensures H2.vmemmap == HP.vmemmap; @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap22_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset24_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr14_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info("/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/\n                  ^./driver.pp.c:1205:19:");
  struct Hyp_pool_record* HP_cn = Hyp_pool(pool_cn, O___hyp_vmemmap22_cn, O_cn_virt_ptr14_cn, O_hyp_physvirt_offset24_cn, GET);
  update_cn_error_message_info("/*@ requires take HP = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1206:24-60 (cursor: 1206:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap22_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n                              ~~~~~~~~~^~ ./driver.pp.c:1207:31-42 (cursor: 1207:40)");
  cn_bits_u64* phys_cn = cn_bits_u64_multiply(p_i_cn, page_size());
  update_cn_error_message_info("/*@ requires let phys = p_i * page_size(); @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1208:25-75 (cursor: 1208:35)");
  cn_pointer* virt_cn = cn__hyp_va(O_cn_virt_ptr14_cn, O_hyp_physvirt_offset24_cn, phys_cn);
  update_cn_error_message_info("/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/\n                                                 ~~~~~~~~~^~ ./driver.pp.c:1209:50-61 (cursor: 1209:59)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(HP_cn->pool->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = HP.pool.range_start / page_size(); @*/\n                                             ~~~~~~~~~^~ ./driver.pp.c:1210:46-57 (cursor: 1210:55)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(HP_cn->pool->range_end, page_size());
  update_cn_error_message_info("/*@ requires let end_i = HP.pool.range_end / page_size(); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1211:14-92 (cursor: 1211:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap22_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_cn));
  cn_bits_u8* order_cn = ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(HP_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->order;
  update_cn_error_message_info("/*@ requires let order = HP.vmemmap[p_i].order; @*/\n                      ~~~~~~~~~~~~~^~ ./driver.pp.c:1213:23-38 (cursor: 1213:36)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_bits_u8_equality(order_cn, hyp_no_order())));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(HP_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->refcount, convert_to_cn_bits_u16(0)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    /*CN*/struct list_head *node = copy_alloc_id((((phys_addr_t)(((phys_addr_t)(((hyp_page_to_pfn(CN_LOAD(p)))) << 12))) - CN_LOAD(hyp_physvirt_offset))), CN_LOAD((cn_virt_ptr)));
c_add_local_to_ghost_state((uintptr_t) &node, sizeof(struct list_head*));

    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/void *node_prev = CN_LOAD(CN_LOAD(node)->prev);
c_add_local_to_ghost_state((uintptr_t) &node_prev, sizeof(void*));

    /*CN*/void *node_next = CN_LOAD(CN_LOAD(node)->next);
c_add_local_to_ghost_state((uintptr_t) &node_next, sizeof(void*));

    /*CN*/
    /*CN*/
        /*CN*/void *free_node = &CN_LOAD(pool)->free_area[CN_LOAD(CN_LOAD(p)->order)];
c_add_local_to_ghost_state((uintptr_t) &free_node, sizeof(void*));

    /*CN*/if (CN_LOAD(node_prev) != CN_LOAD(node)) {
        /*CN*/if (CN_LOAD(node_prev) != CN_LOAD(free_node))
        ;
        /*CN*/if (CN_LOAD(node_next) != CN_LOAD(node_prev) && CN_LOAD(node_next) != CN_LOAD(free_node))
        ;
    /*CN*/};
    page_remove_from_list(CN_LOAD(p));

c_remove_local_from_ghost_state((uintptr_t) &node, sizeof(struct list_head*));


c_remove_local_from_ghost_state((uintptr_t) &node_prev, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &node_next, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &free_node, sizeof(void*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap23_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset25_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr15_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires HP.vmemmap[p_i].refcount == 0u16; @*/\n                 ^./driver.pp.c:1215:18:");
  ZeroPage(virt_cn, convert_to_cn_bool(true), order_cn, PUT);
  update_cn_error_message_info("/*@ ensures take ZP = ZeroPage(virt, true, order); @*/\n                 ^./driver.pp.c:1216:18:");
  struct Hyp_pool_ex1_record* H2_cn = Hyp_pool_ex1(pool_cn, O___hyp_vmemmap23_cn, O_cn_virt_ptr15_cn, O_hyp_physvirt_offset25_cn, p_i_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1217:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap23_cn, O___hyp_vmemmap22_cn));
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1217:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset25_cn, O_hyp_physvirt_offset24_cn));
  update_cn_error_message_info("/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1218:13-38");
  cn_assert(cn_map_equality(H2_cn->vmemmap, HP_cn->vmemmap, struct_hyp_page_cn_equality));
  struct hyp_pool_cn* a_9358 = alloc(sizeof(struct hyp_pool_cn));
  a_9358->free_area = H2_cn->pool->free_area;
  a_9358->range_start = HP_cn->pool->range_start;
  a_9358->range_end = HP_cn->pool->range_end;
  a_9358->max_order = HP_cn->pool->max_order;
  update_cn_error_message_info("/*@ ensures H2.vmemmap == HP.vmemmap; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1219:13-66");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, a_9358));
  ghost_stack_depth_decr();
}
;
}
static inline void page_add_to_list(struct hyp_page *p, struct list_head *head)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires let phys = p_i * page_size(); @*/
/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/
/*@ requires take Hp = Owned(p); @*/
/*@ requires let order = (*p).order; @*/
/*@ requires order < 11u8; @*/
/*@ requires take AP1 = ZeroPage(virt, true, order); @*/
/*@ requires let next = head; @*/
/*@ requires take Node_head = Owned<struct list_head>(next); @*/
/*@ requires let prev = (*next).prev; @*/
/*@ requires ptr_eq(prev, next) || !addr_eq(prev, next); @*/
/*@ requires take Node_prev = O_struct_list_head(prev, !addr_eq(prev, next)); @*/
/*@ requires (u64) hyp_physvirt_offset / page_size() <= p_i; p_i < shift_left(1u64, 63u64) / page_size(); @*/
/*@ requires (mod((u64) hyp_physvirt_offset, page_size())) == 0u64; @*/
/*@ requires phys > (u64) hyp_physvirt_offset; @*/
/*@ requires p >= __hyp_vmemmap; @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {cn_virt_ptr} unchanged; @*/
/*@ ensures take AP1R = AllocatorPage(virt, true, order); @*/
/*@ ensures take Hp2 = Owned(p); @*/
/*@ ensures {*p} unchanged; @*/
/*@ ensures take Node_head2 = Owned<struct list_head>(next); @*/
/*@ ensures take Node_prev2 = O_struct_list_head(prev, !addr_eq(prev, next)); @*/
/*@ ensures (prev == next) || (Node_prev.prev == Node_prev2.prev); @*/
/*@ ensures (prev == next) || {(*next).next} unchanged; @*/
/*@ ensures (*next).prev == virt; @*/
/*@ ensures (prev == next) || (Node_prev2.next == virt); @*/
/*@ ensures !addr_eq(prev, next) || ((*next).next == virt); @*/
/*@ ensures (AP1R.next == head); (AP1R.prev == prev); @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  cn_pointer* head_cn = convert_to_cn_pointer(head);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap24_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset26_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr16_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info("/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1243:24-60 (cursor: 1243:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap24_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n                              ~~~~~~~~~^~ ./driver.pp.c:1244:31-42 (cursor: 1244:40)");
  cn_bits_u64* phys_cn = cn_bits_u64_multiply(p_i_cn, page_size());
  update_cn_error_message_info("/*@ requires let phys = p_i * page_size(); @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1245:25-75 (cursor: 1245:35)");
  cn_pointer* virt_cn = cn__hyp_va(O_cn_virt_ptr16_cn, O_hyp_physvirt_offset26_cn, phys_cn);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* Hp_cn = owned_struct_hyp_page(p_cn, GET);
  cn_bits_u8* order_cn = Hp_cn->order;
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u8_lt(order_cn, convert_to_cn_bits_u8(11)));
  update_cn_error_message_info("/*@ requires order < 11u8; @*/\n                  ^./driver.pp.c:1249:19:");
  ZeroPage(virt_cn, convert_to_cn_bool(true), order_cn, GET);
  cn_pointer* next_cn = head_cn;
  update_cn_error_message_info("unknown location");
  struct list_head_cn* Node_head_cn = owned_struct_list_head(next_cn, GET);
  cn_pointer* prev_cn = Node_head_cn->prev;
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(prev_cn), cast_cn_pointer_to_cn_bits_u64(next_cn)))));
  update_cn_error_message_info("/*@ requires ptr_eq(prev, next) || !addr_eq(prev, next); @*/\n                  ^./driver.pp.c:1254:19:");
  struct list_head_cn* Node_prev_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(prev_cn), cast_cn_pointer_to_cn_bits_u64(next_cn))), GET);
  update_cn_error_message_info("/*@ requires take Node_prev = O_struct_list_head(prev, !addr_eq(prev, next)); @*/\n                                         ~~~~~~~~~^~ ./driver.pp.c:1255:42-53 (cursor: 1255:51)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(cn_bits_u64_divide(cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset26_cn), page_size()), p_i_cn));
  update_cn_error_message_info("/*@ requires take Node_prev = O_struct_list_head(prev, !addr_eq(prev, next)); @*/\n                                                                                             ~~~~~~~~~^~ ./driver.pp.c:1255:94-105 (cursor: 1255:103)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(p_i_cn, cn_bits_u64_divide(cn_bits_u64_shift_left(convert_to_cn_bits_u64(1), convert_to_cn_bits_u64(63)), page_size())));
  update_cn_error_message_info("/*@ requires (u64) hyp_physvirt_offset / page_size() <= p_i; p_i < shift_left(1u64, 63u64) / page_size(); @*/\n                                             ~~~~~~~~~^~ ./driver.pp.c:1256:46-57 (cursor: 1256:55)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_equality(cn_bits_u64_mod(cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset26_cn), page_size()), convert_to_cn_bits_u64(0)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset26_cn), phys_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_pointer_le(O___hyp_vmemmap24_cn, p_cn));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  c_add_local_to_ghost_state((uintptr_t) &head, sizeof(struct list_head*));
  
    struct list_head *node = copy_alloc_id((((phys_addr_t)(((phys_addr_t)(((hyp_page_to_pfn(CN_LOAD(p)))) << 12))) - CN_LOAD(hyp_physvirt_offset))), CN_LOAD((cn_virt_ptr)));
c_add_local_to_ghost_state((uintptr_t) &node, sizeof(struct list_head*));

    /*CN*/if (CN_LOAD(CN_LOAD(head)->prev) != CN_LOAD(head)) {}
    /*CN*/
    INIT_LIST_HEAD(CN_LOAD(node));
    list_add_tail(CN_LOAD(node), CN_LOAD(head));

c_remove_local_from_ghost_state((uintptr_t) &node, sizeof(struct list_head*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

  c_remove_local_from_ghost_state((uintptr_t) &head, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap25_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset27_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr17_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires p >= __hyp_vmemmap; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1259:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap25_cn, O___hyp_vmemmap24_cn));
  update_cn_error_message_info("/*@ requires p >= __hyp_vmemmap; @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1259:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset27_cn, O_hyp_physvirt_offset26_cn));
  update_cn_error_message_info("/*@ requires p >= __hyp_vmemmap; @*/\n                                                                        ^~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1259:73-97");
  cn_assert(cn_pointer_equality(O_cn_virt_ptr17_cn, O_cn_virt_ptr16_cn));
  update_cn_error_message_info("/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {cn_virt_ptr} unchanged; @*/\n                 ^./driver.pp.c:1260:18:");
  struct list_head_cn* AP1R_cn = AllocatorPage(virt_cn, convert_to_cn_bool(true), order_cn, PUT);
  update_cn_error_message_info("unknown location");
  struct hyp_page_cn* Hp2_cn = owned_struct_hyp_page(p_cn, PUT);
  update_cn_error_message_info("/*@ ensures take Hp2 = Owned(p); @*/\n            ^~~~~~~~~~~~~~~ ./driver.pp.c:1262:13-28");
  cn_assert(struct_hyp_page_cn_equality(Hp2_cn, Hp_cn));
  update_cn_error_message_info("unknown location");
  struct list_head_cn* Node_head2_cn = owned_struct_list_head(next_cn, PUT);
  update_cn_error_message_info("/*@ ensures take Node_head2 = Owned<struct list_head>(next); @*/\n                 ^./driver.pp.c:1264:18:");
  struct list_head_cn* Node_prev2_cn = O_struct_list_head(prev_cn, cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(prev_cn), cast_cn_pointer_to_cn_bits_u64(next_cn))), PUT);
  update_cn_error_message_info("/*@ ensures take Node_prev2 = O_struct_list_head(prev, !addr_eq(prev, next)); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1265:13-67");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(Node_prev_cn->prev, Node_prev2_cn->prev)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (Node_prev.prev == Node_prev2.prev); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1266:13-56");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(Node_head2_cn->next, Node_head_cn->next)));
  update_cn_error_message_info("/*@ ensures (prev == next) || {(*next).next} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1267:13-34");
  cn_assert(cn_pointer_equality(Node_head2_cn->prev, virt_cn));
  update_cn_error_message_info("/*@ ensures (*next).prev == virt; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1268:13-57");
  cn_assert(cn_bool_or(cn_pointer_equality(prev_cn, next_cn), cn_pointer_equality(Node_prev2_cn->next, virt_cn)));
  update_cn_error_message_info("/*@ ensures (prev == next) || (Node_prev2.next == virt); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1269:13-60");
  cn_assert(cn_bool_or(cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(prev_cn), cast_cn_pointer_to_cn_bits_u64(next_cn))), cn_pointer_equality(Node_head2_cn->next, virt_cn)));
  update_cn_error_message_info("/*@ ensures !addr_eq(prev, next) || ((*next).next == virt); @*/\n            ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1270:13-33");
  cn_assert(cn_pointer_equality(AP1R_cn->next, head_cn));
  update_cn_error_message_info("/*@ ensures !addr_eq(prev, next) || ((*next).next == virt); @*/\n                                 ^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1270:34-54");
  cn_assert(cn_pointer_equality(AP1R_cn->prev, prev_cn));
  ghost_stack_depth_decr();
}
;
}
static inline void page_add_to_list_pool(struct hyp_pool *pool,
                struct hyp_page *p, struct list_head *head)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/
/*@ requires p >= __hyp_vmemmap; @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires take HP = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/
/*@ requires let free_area_l = member_shift<hyp_pool>(pool, free_area); @*/
/*@ requires let phys = p_i * page_size(); @*/
/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/
/*@ requires let virt_i = (u64) virt / page_size(); @*/
/*@ requires let start_i = HP.pool.range_start / page_size(); @*/
/*@ requires let end_i = HP.pool.range_end / page_size(); @*/
/*@ requires (u64) hyp_physvirt_offset / page_size() <= p_i; p_i < shift_left(1u64, 63u64) / page_size(); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/
/*@ requires let order = (HP.vmemmap[p_i]).order; @*/
/*@ requires order != (hyp_no_order ()); @*/
/*@ requires HP.vmemmap[p_i].refcount == 0u16; @*/
/*@ requires take ZP = ZeroPage(virt, true, order); @*/
/*@ requires head == array_shift<struct list_head>(&(pool->free_area), order); @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; @*/
/*@ ensures H2.vmemmap == HP.vmemmap; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  cn_pointer* head_cn = convert_to_cn_pointer(head);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap26_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset28_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr18_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_pointer_le(O___hyp_vmemmap26_cn, p_cn));
  update_cn_error_message_info("/*@ requires p >= __hyp_vmemmap; @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1283:24-60 (cursor: 1283:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap26_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n                  ^./driver.pp.c:1284:19:");
  struct Hyp_pool_ex1_record* HP_cn = Hyp_pool_ex1(pool_cn, O___hyp_vmemmap26_cn, O_cn_virt_ptr18_cn, O_hyp_physvirt_offset28_cn, p_i_cn, GET);
  cn_pointer* free_area_l_cn = cn_member_shift(pool_cn, hyp_pool, free_area);
  update_cn_error_message_info("/*@ requires let free_area_l = member_shift<hyp_pool>(pool, free_area); @*/\n                              ~~~~~~~~~^~ ./driver.pp.c:1286:31-42 (cursor: 1286:40)");
  cn_bits_u64* phys_cn = cn_bits_u64_multiply(p_i_cn, page_size());
  update_cn_error_message_info("/*@ requires let phys = p_i * page_size(); @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1287:25-75 (cursor: 1287:35)");
  cn_pointer* virt_cn = cn__hyp_va(O_cn_virt_ptr18_cn, O_hyp_physvirt_offset28_cn, phys_cn);
  update_cn_error_message_info("/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/\n                                       ~~~~~~~~~^~ ./driver.pp.c:1288:40-51 (cursor: 1288:49)");
  cn_bits_u64* virt_i_cn = cn_bits_u64_divide(cast_cn_pointer_to_cn_bits_u64(virt_cn), page_size());
  update_cn_error_message_info("/*@ requires let virt_i = (u64) virt / page_size(); @*/\n                                                 ~~~~~~~~~^~ ./driver.pp.c:1289:50-61 (cursor: 1289:59)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(HP_cn->pool->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = HP.pool.range_start / page_size(); @*/\n                                             ~~~~~~~~~^~ ./driver.pp.c:1290:46-57 (cursor: 1290:55)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(HP_cn->pool->range_end, page_size());
  update_cn_error_message_info("/*@ requires let end_i = HP.pool.range_end / page_size(); @*/\n                                         ~~~~~~~~~^~ ./driver.pp.c:1291:42-53 (cursor: 1291:51)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(cn_bits_u64_divide(cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset28_cn), page_size()), p_i_cn));
  update_cn_error_message_info("/*@ requires let end_i = HP.pool.range_end / page_size(); @*/\n                                                                                             ~~~~~~~~~^~ ./driver.pp.c:1291:94-105 (cursor: 1291:103)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(p_i_cn, cn_bits_u64_divide(cn_bits_u64_shift_left(convert_to_cn_bits_u64(1), convert_to_cn_bits_u64(63)), page_size())));
  update_cn_error_message_info("/*@ requires (u64) hyp_physvirt_offset / page_size() <= p_i; p_i < shift_left(1u64, 63u64) / page_size(); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1292:14-92 (cursor: 1292:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap26_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_cn));
  cn_bits_u8* order_cn = ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(HP_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->order;
  update_cn_error_message_info("/*@ requires let order = (HP.vmemmap[p_i]).order; @*/\n                       ~~~~~~~~~~~~~^~ ./driver.pp.c:1294:24-39 (cursor: 1294:37)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_bits_u8_equality(order_cn, hyp_no_order())));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(HP_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->refcount, convert_to_cn_bits_u16(0)));
  update_cn_error_message_info("/*@ requires HP.vmemmap[p_i].refcount == 0u16; @*/\n                  ^./driver.pp.c:1296:19:");
  ZeroPage(virt_cn, convert_to_cn_bool(true), order_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_pointer_equality(head_cn, cn_array_shift(cn_member_shift(pool_cn, hyp_pool, free_area), sizeof(struct list_head), order_cn)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  c_add_local_to_ghost_state((uintptr_t) &head, sizeof(struct list_head*));
  
    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/struct list_head *prev = CN_LOAD(CN_LOAD(head)->prev);
c_add_local_to_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));

    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/if (CN_LOAD(prev) != CN_LOAD(head)) {
        /*CN*/
        /*CN*/
        CN_LOAD(*CN_LOAD(prev));
    /*CN*/};
    cn_pointer* read_prev5 = convert_to_cn_pointer(cn_pointer_deref(convert_to_cn_pointer((&prev)), struct list_head*));

cn_pointer* read_head2 = convert_to_cn_pointer(cn_pointer_deref(convert_to_cn_pointer((&head)), struct list_head*));

cn_pointer* read_prev6 = convert_to_cn_pointer(cn_pointer_deref(convert_to_cn_pointer((&prev)), struct list_head*));

cn_pointer* read_head3 = convert_to_cn_pointer(cn_pointer_deref(convert_to_cn_pointer((&head)), struct list_head*));

update_cn_error_message_info(NULL);

cn_assert(cn_bool_or(cn_pointer_equality(read_prev5, read_head2), cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(read_prev6), cast_cn_pointer_to_cn_bits_u64(read_head3)))));

    page_add_to_list(CN_LOAD(p), CN_LOAD(head));

c_remove_local_from_ghost_state((uintptr_t) &prev, sizeof(struct list_head*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

  c_remove_local_from_ghost_state((uintptr_t) &head, sizeof(struct list_head*));

{
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap27_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset29_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr19_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires head == array_shift<struct list_head>(&(pool->free_area), order); @*/\n                 ^./driver.pp.c:1298:18:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, O___hyp_vmemmap27_cn, O_cn_virt_ptr19_cn, O_hyp_physvirt_offset29_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1299:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap27_cn, O___hyp_vmemmap26_cn));
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1299:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset29_cn, O_hyp_physvirt_offset28_cn));
  struct hyp_pool_cn* a_9977 = alloc(sizeof(struct hyp_pool_cn));
  a_9977->free_area = H2_cn->pool->free_area;
  a_9977->range_start = HP_cn->pool->range_start;
  a_9977->range_end = HP_cn->pool->range_end;
  a_9977->max_order = HP_cn->pool->max_order;
  update_cn_error_message_info("/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1300:13-66");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, a_9977));
  update_cn_error_message_info("/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1301:13-38");
  cn_assert(cn_map_equality(H2_cn->vmemmap, HP_cn->vmemmap, struct_hyp_page_cn_equality));
  ghost_stack_depth_decr();
}
;
}
static inline void page_add_to_list_pool_ex1(struct hyp_pool *pool,
                struct hyp_page *p, struct list_head *head, struct hyp_page *p_ex)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/
/*@ requires let p_i2 = cn_hyp_page_to_pfn(__hyp_vmemmap, p_ex); @*/
/*@ requires take HP = Hyp_pool_ex2(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i, p_i2); @*/
/*@ requires let free_area_l = member_shift<hyp_pool>(pool, free_area); @*/
/*@ requires let phys = p_i * page_size(); @*/
/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/
/*@ requires let start_i = HP.pool.range_start / page_size(); @*/
/*@ requires let end_i = HP.pool.range_end / page_size(); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p_ex); @*/
/*@ requires let order = (HP.vmemmap[p_i]).order; @*/
/*@ requires order != hyp_no_order (); @*/
/*@ requires (HP.vmemmap[p_i]).refcount == 0u16; @*/
/*@ requires take ZP = ZeroPage(virt, true, order); @*/
/*@ requires head == array_shift<struct list_head>(&(pool->free_area), order); @*/
/*@ requires p_i != p_i2; @*/
/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i2); @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; @*/
/*@ ensures H2.vmemmap == HP.vmemmap; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  cn_pointer* head_cn = convert_to_cn_pointer(head);
  cn_pointer* p_ex_cn = convert_to_cn_pointer(p_ex);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap28_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset30_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr20_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info("/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1322:24-60 (cursor: 1322:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap28_cn, p_cn);
  update_cn_error_message_info(NULL);
  cn_assert(cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0)));
  update_cn_error_message_info("/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/\n                        ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1324:25-64 (cursor: 1324:43)");
  cn_bits_u64* p_i2_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap28_cn, p_ex_cn);
  update_cn_error_message_info("/*@ requires let p_i2 = cn_hyp_page_to_pfn(__hyp_vmemmap, p_ex); @*/\n                  ^./driver.pp.c:1325:19:");
  struct Hyp_pool_ex2_record* HP_cn = Hyp_pool_ex2(pool_cn, O___hyp_vmemmap28_cn, O_cn_virt_ptr20_cn, O_hyp_physvirt_offset30_cn, p_i_cn, p_i2_cn, GET);
  cn_pointer* free_area_l_cn = cn_member_shift(pool_cn, hyp_pool, free_area);
  update_cn_error_message_info("/*@ requires let free_area_l = member_shift<hyp_pool>(pool, free_area); @*/\n                              ~~~~~~~~~^~ ./driver.pp.c:1327:31-42 (cursor: 1327:40)");
  cn_bits_u64* phys_cn = cn_bits_u64_multiply(p_i_cn, page_size());
  update_cn_error_message_info("/*@ requires let phys = p_i * page_size(); @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1328:25-75 (cursor: 1328:35)");
  cn_pointer* virt_cn = cn__hyp_va(O_cn_virt_ptr20_cn, O_hyp_physvirt_offset30_cn, phys_cn);
  update_cn_error_message_info("/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/\n                                                 ~~~~~~~~~^~ ./driver.pp.c:1329:50-61 (cursor: 1329:59)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(HP_cn->pool->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = HP.pool.range_start / page_size(); @*/\n                                             ~~~~~~~~~^~ ./driver.pp.c:1330:46-57 (cursor: 1330:55)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(HP_cn->pool->range_end, page_size());
  update_cn_error_message_info("/*@ requires let end_i = HP.pool.range_end / page_size(); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1331:14-92 (cursor: 1331:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap28_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_cn));
  update_cn_error_message_info("/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1332:14-95 (cursor: 1332:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap28_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_ex_cn));
  cn_bits_u8* order_cn = ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(HP_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->order;
  update_cn_error_message_info("/*@ requires let order = (HP.vmemmap[p_i]).order; @*/\n                      ~~~~~~~~~~~~~^~ ./driver.pp.c:1334:23-38 (cursor: 1334:36)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_bits_u8_equality(order_cn, hyp_no_order())));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(HP_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->refcount, convert_to_cn_bits_u16(0)));
  update_cn_error_message_info("/*@ requires (HP.vmemmap[p_i]).refcount == 0u16; @*/\n                  ^./driver.pp.c:1336:19:");
  ZeroPage(virt_cn, convert_to_cn_bool(true), order_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_pointer_equality(head_cn, cn_array_shift(cn_member_shift(pool_cn, hyp_pool, free_area), sizeof(struct list_head), order_cn)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_bits_u64_equality(p_i_cn, p_i2_cn)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  c_add_local_to_ghost_state((uintptr_t) &head, sizeof(struct list_head*));
  c_add_local_to_ghost_state((uintptr_t) &p_ex, sizeof(struct hyp_page*));
  
    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/void *prev = CN_LOAD(CN_LOAD(head)->prev);
c_add_local_to_ghost_state((uintptr_t) &prev, sizeof(void*));

    /*CN*/
    /*CN*/
    /*CN*/
    /*CN*/if (CN_LOAD(prev) != CN_LOAD(head)) {
        /*CN*/
    /*CN*/};
    page_add_to_list(CN_LOAD(p), CN_LOAD(head));

c_remove_local_from_ghost_state((uintptr_t) &prev, sizeof(void*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

  c_remove_local_from_ghost_state((uintptr_t) &head, sizeof(struct list_head*));

  c_remove_local_from_ghost_state((uintptr_t) &p_ex, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap29_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset31_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr21_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires p_i != p_i2; @*/\n                 ^./driver.pp.c:1339:18:");
  struct Hyp_pool_ex1_record* H2_cn = Hyp_pool_ex1(pool_cn, O___hyp_vmemmap29_cn, O_cn_virt_ptr21_cn, O_hyp_physvirt_offset31_cn, p_i2_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i2); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1340:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap29_cn, O___hyp_vmemmap28_cn));
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i2); @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1340:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset31_cn, O_hyp_physvirt_offset30_cn));
  struct hyp_pool_cn* a_10261 = alloc(sizeof(struct hyp_pool_cn));
  a_10261->free_area = H2_cn->pool->free_area;
  a_10261->range_start = HP_cn->pool->range_start;
  a_10261->range_end = HP_cn->pool->range_end;
  a_10261->max_order = HP_cn->pool->max_order;
  update_cn_error_message_info("/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1341:13-66");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, a_10261));
  update_cn_error_message_info("/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1342:13-38");
  cn_assert(cn_map_equality(H2_cn->vmemmap, HP_cn->vmemmap, struct_hyp_page_cn_equality));
  ghost_stack_depth_decr();
}
;
}
static inline struct hyp_page *node_to_page(struct list_head *node)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; @*/
/*@ requires 0i64 <= hyp_physvirt_offset; @*/
/*@ requires let phys = (u64) node + (u64) hyp_physvirt_offset; @*/
/*@ requires let p_i = phys / page_size(); @*/
/*@ requires let page = array_shift<struct hyp_page>(__hyp_vmemmap, p_i); @*/
/*@ requires mod((u64) hyp_physvirt_offset, page_size ()) == 0u64; @*/
/*@ requires mod((u64) __hyp_vmemmap, (u64) (sizeof<struct hyp_page>)) == 0u64; @*/
/*@ ensures return == page; @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  struct hyp_page* __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* node_cn = convert_to_cn_pointer(node);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap30_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset32_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_i64_le(convert_to_cn_bits_i64(0), O_hyp_physvirt_offset32_cn));
  cn_bits_u64* phys_cn = cn_bits_u64_add(cast_cn_pointer_to_cn_bits_u64(node_cn), cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset32_cn));
  update_cn_error_message_info("/*@ requires let phys = (u64) node + (u64) hyp_physvirt_offset; @*/\n                              ~~~~~~~~~^~ ./driver.pp.c:1361:31-42 (cursor: 1361:40)");
  cn_bits_u64* p_i_cn = cn_bits_u64_divide(phys_cn, page_size());
  cn_pointer* page_cn = cn_array_shift(O___hyp_vmemmap30_cn, sizeof(struct hyp_page), p_i_cn);
  update_cn_error_message_info("/*@ requires let page = array_shift<struct hyp_page>(__hyp_vmemmap, p_i); @*/\n                                            ~~~~~~~~~~^~ ./driver.pp.c:1363:45-57 (cursor: 1363:55)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_equality(cn_bits_u64_mod(cast_cn_bits_i64_to_cn_bits_u64(O_hyp_physvirt_offset32_cn), page_size()), convert_to_cn_bits_u64(0)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_equality(cn_bits_u64_mod(cast_cn_pointer_to_cn_bits_u64(O___hyp_vmemmap30_cn), cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page)))), convert_to_cn_bits_u64(0)));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &node, sizeof(struct list_head*));
  
    { __cn_ret = (&((struct hyp_page *)CN_LOAD(__hyp_vmemmap))[((((phys_addr_t)CN_LOAD((node)) + CN_LOAD(hyp_physvirt_offset))) >> 12)]); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &node, sizeof(struct list_head*));

{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap31_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset33_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("/*@ requires mod((u64) __hyp_vmemmap, (u64) (sizeof<struct hyp_page>)) == 0u64; @*/\n            ^~~~~~~~~~~~~~~ ./driver.pp.c:1365:13-28");
  cn_assert(cn_pointer_equality(return_cn, page_cn));
  update_cn_error_message_info("/*@ ensures return == page; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1366:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap31_cn, O___hyp_vmemmap30_cn));
  update_cn_error_message_info("/*@ ensures return == page; @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1366:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset33_cn, O_hyp_physvirt_offset32_cn));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
static void __hyp_attach_page(struct hyp_pool *pool,
                  struct hyp_page *p)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires take H = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/
/*@ requires let start_i = H.pool.range_start / page_size(); @*/
/*@ requires let end_i = H.pool.range_end / page_size (); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/
/*@ requires (H.vmemmap[p_i]).refcount == 0u16; @*/
/*@ requires ((H.vmemmap[p_i]).order) != (hyp_no_order()); @*/
/*@ requires let i_order = (H.vmemmap[p_i]).order; @*/
/*@ requires (p_i * page_size()) + (page_size_of_order(i_order)) <= (H.pool).range_end; @*/
/*@ requires let ptr_phys_0 = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, 0u64); @*/
/*@ requires take P = Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, p_i), true, i_order); @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ ensures {free_area: H2.pool.free_area, ..H.pool} == H2.pool; @*/
/*@ ensures each (u64 i; p_i < i && i < end_i){(H.vmemmap[i].refcount == 0u16) || (H2.vmemmap[i] == H.vmemmap[i])}; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap32_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset34_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr22_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0)));
  update_cn_error_message_info("/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1374:24-60 (cursor: 1374:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap32_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n                  ^./driver.pp.c:1375:19:");
  struct Hyp_pool_ex1_record* H_cn = Hyp_pool_ex1(pool_cn, O___hyp_vmemmap32_cn, O_cn_virt_ptr22_cn, O_hyp_physvirt_offset34_cn, p_i_cn, GET);
  update_cn_error_message_info("/*@ requires take H = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/\n                                                ~~~~~~~~~^~ ./driver.pp.c:1376:49-60 (cursor: 1376:58)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(H_cn->pool->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = H.pool.range_start / page_size(); @*/\n                                            ~~~~~~~~~~^~ ./driver.pp.c:1377:45-57 (cursor: 1377:55)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(H_cn->pool->range_end, page_size());
  update_cn_error_message_info("/*@ requires let end_i = H.pool.range_end / page_size (); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1378:14-92 (cursor: 1378:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap32_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->refcount, convert_to_cn_bits_u16(0)));
  update_cn_error_message_info("/*@ requires (H.vmemmap[p_i]).refcount == 0u16; @*/\n                                          ~~~~~~~~~~~~^~ ./driver.pp.c:1380:43-57 (cursor: 1380:55)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->order, hyp_no_order())));
  cn_bits_u8* i_order_cn = ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->order;
  update_cn_error_message_info("/*@ requires let i_order = (H.vmemmap[p_i]).order; @*/\n                    ~~~~~~~~~^~ ./driver.pp.c:1382:21-32 (cursor: 1382:30)");
  update_cn_error_message_info("/*@ requires let i_order = (H.vmemmap[p_i]).order; @*/\n                                    ~~~~~~~~~~~~~~~~~~^~~~~~~~~ ./driver.pp.c:1382:37-64 (cursor: 1382:55)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(cn_bits_u64_add(cn_bits_u64_multiply(p_i_cn, page_size()), page_size_of_order(i_order_cn)), H_cn->pool->range_end));
  update_cn_error_message_info("/*@ requires (p_i * page_size()) + (page_size_of_order(i_order)) <= (H.pool).range_end; @*/\n                              ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1383:31-81 (cursor: 1383:41)");
  cn_pointer* ptr_phys_0_cn = cn__hyp_va(O_cn_virt_ptr22_cn, O_hyp_physvirt_offset34_cn, convert_to_cn_bits_u64(0));
  update_cn_error_message_info("/*@ requires let ptr_phys_0 = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, 0u64); @*/\n                  ^./driver.pp.c:1384:19:");
  Page(cn_array_shift(ptr_phys_0_cn, sizeof(char[4096]), p_i_cn), convert_to_cn_bool(true), i_order_cn, GET);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    /*CN*/
    phys_addr_t phys = ((phys_addr_t)(((hyp_page_to_pfn(CN_LOAD(p)))) << 12));
c_add_local_to_ghost_state((uintptr_t) &phys, sizeof(unsigned long long));

    /* struct hyp_page *buddy; */
    struct hyp_page *buddy = ((void *)0);
c_add_local_to_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));

    /*CN*/
    u8 order = CN_LOAD(CN_LOAD(p)->order);
c_add_local_to_ghost_state((uintptr_t) &order, sizeof(unsigned char));

        /*CN*/
    memset(copy_alloc_id((((phys_addr_t)(((phys_addr_t)(((hyp_page_to_pfn(CN_LOAD(p)))) << 12))) - CN_LOAD(hyp_physvirt_offset))), CN_LOAD((cn_virt_ptr))), 0, ((1UL) << 12) << CN_LOAD(CN_LOAD(p)->order));
    //if (phys < pool->range_start || phys >= pool->range_end)
    //    goto insert;
    if (!(CN_LOAD(phys) < CN_LOAD(CN_LOAD(pool)->range_start) || CN_LOAD(phys) >= CN_LOAD(CN_LOAD(pool)->range_end))) {
        /*
         * Only the first struct hyp_page of a high-order page (otherwise known
         * as the 'head') should have p->order set. The non-head pages should
         * have p->order = HYP_NO_ORDER. Here @p may no longer be the head
         * after coallescing, so make sure to mark it HYP_NO_ORDER proactively.
         */
        CN_STORE(CN_LOAD(p)->order, 0xff);
        for (; (CN_LOAD(order) + 1) < CN_LOAD(CN_LOAD(pool)->max_order); CN_POSTFIX(order, ++))
        /*@ inv (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/
        /*@ inv let p_i2 = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
        /*@ inv let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, p_i2 * page_size()); @*/
        /*@ inv take Z = ZeroPage(virt, true, order); @*/
        /*@ inv take H_I = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
        /*@ inv let p_page = H_I.vmemmap[p_i2]; @*/
        /* for page_group_ok */
        /*@ inv each (u64 i; (start_i <= i) && (i < end_i))
            {vmemmap_wf (i, (H_I.vmemmap)[p_i2: {order: order, ..p_page}], pool, H_I.pool)}; @*/
        /*@ inv order < H_I.pool.max_order; @*/
        /*@ inv cellPointer(__hyp_vmemmap,(u64) (sizeof<struct hyp_page>),start_i,end_i,p); @*/
        /*@ inv p_page.refcount == 0u16; p_page.order == hyp_no_order (); @*/
        /*@ inv order_aligned(p_i2,order); @*/
        /*@ inv (p_i2 * page_size()) + (page_size_of_order(order)) <= (H_I.pool).range_end; @*/
        /*@ inv each (u64 i; p_i < i && i < end_i)
            {(H.vmemmap[i].refcount == 0u16) || (H_I.vmemmap[i] == H.vmemmap[i])}; @*/
        /*@ inv {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {pool} unchanged; @*/
        /*@ inv H_I.pool == {free_area: (H_I.pool).free_area, ..H.pool}; @*/
        {
            CN_STORE(buddy, __find_buddy_avail(CN_LOAD(pool), CN_LOAD(p), CN_LOAD(order)));
            if (!CN_LOAD(buddy))
                break;
            /*CN*/
            /*CN*/
            /*CN*/
            /*CN*/
            /*CN*/
            /*CN*/
            /* Take the buddy out of its list, and coallesce with @p */
            page_remove_from_list_pool(CN_LOAD(pool), CN_LOAD(buddy));
            CN_STORE(CN_LOAD(buddy)->order, 0xff);
            CN_STORE(p, (CN_LOAD((p)) < CN_LOAD((buddy)) ? CN_LOAD((p)) : CN_LOAD((buddy))));
        }
    }
//insert:
    /*CN*/
    /*CN*/
    /* Mark the new head, and insert it */
    CN_STORE(CN_LOAD(p)->order, CN_LOAD(order));
    /*CN*/
    page_add_to_list_pool(CN_LOAD(pool), CN_LOAD(p), &CN_LOAD(pool)->free_area[CN_LOAD(order)]);

c_remove_local_from_ghost_state((uintptr_t) &phys, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &order, sizeof(unsigned char));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap33_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset35_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr23_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires take P = Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, p_i), true, i_order); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1385:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap33_cn, O___hyp_vmemmap32_cn));
  update_cn_error_message_info("/*@ requires take P = Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, p_i), true, i_order); @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1385:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset35_cn, O_hyp_physvirt_offset34_cn));
  update_cn_error_message_info("/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/\n                 ^./driver.pp.c:1386:18:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, O___hyp_vmemmap33_cn, O_cn_virt_ptr23_cn, O_hyp_physvirt_offset35_cn, PUT);
  struct hyp_pool_cn* a_10716 = alloc(sizeof(struct hyp_pool_cn));
  a_10716->free_area = H2_cn->pool->free_area;
  a_10716->range_start = H_cn->pool->range_start;
  a_10716->range_end = H_cn->pool->range_end;
  a_10716->max_order = H_cn->pool->max_order;
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1387:13-65");
  cn_assert(struct_hyp_pool_cn_equality(a_10716, H2_cn->pool));
  cn_bool* a_10764 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(cn_bits_u64_add(p_i_cn, convert_to_cn_bits_u64(1)));
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_lt(p_i_cn, i), cn_bits_u64_lt(i, end_i_cn)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        a_10764 = cn_bool_and(a_10764, cn_bool_or(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), struct_hyp_page_cn_equality((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H2_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(i)), (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(i)))));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info("/*@ ensures {free_area: H2.pool.free_area, ..H.pool} == H2.pool; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1388:13-116");
  cn_assert(a_10764);
  ghost_stack_depth_decr();
}
;
}
static struct hyp_page *__hyp_extract_page(struct hyp_pool *pool,
                       struct hyp_page *p,
                       u8 order)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), H.pool.range_start / page_size(), H.pool.range_end / page_size(), p); @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires let p_order = (H.vmemmap[p_i]).order; @*/
/*@ requires H.vmemmap[p_i].refcount == 0u16; @*/
/*@ requires (H.APs[p_i]).prev == array_shift<struct list_head>(&(pool->free_area), p_order); @*/
/*@ requires order <= p_order; p_order != (hyp_no_order ()); @*/
/*@ requires order_aligned(p_i, order); @*/
/*@ requires let start_i = H.pool.range_start / (page_size()); @*/
/*@ requires let end_i = H.pool.range_end / page_size(); @*/
/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/
/*@ ensures let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, p_i * page_size()); @*/
/*@ ensures take ZR = ZeroPage(virt, true, order); @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
/*@ ensures H2.pool == {free_area: (H2.pool).free_area, ..H.pool}; @*/
/*@ ensures return == p; @*/
/*@ ensures let p_page = H2.vmemmap[p_i]; @*/
/*@ ensures p_page.refcount == 0u16; p_page.order == order; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  struct hyp_page* __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  cn_bits_u8* order_cn = convert_to_cn_bits_u8(order);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap35_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset37_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr25_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0)));
  update_cn_error_message_info("/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/\n                  ^./driver.pp.c:1456:19:");
  struct Hyp_pool_record* H_cn = Hyp_pool(pool_cn, O___hyp_vmemmap35_cn, O_cn_virt_ptr25_cn, O_hyp_physvirt_offset37_cn, GET);
  update_cn_error_message_info("/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                                                                                              ~~~~~~~~~^~ ./driver.pp.c:1457:95-106 (cursor: 1457:104)");
  update_cn_error_message_info("/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                                                                                                                              ~~~~~~~~~^~ ./driver.pp.c:1457:127-138 (cursor: 1457:136)");
  update_cn_error_message_info("/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1457:14-142 (cursor: 1457:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap35_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), cn_bits_u64_divide(H_cn->pool->range_start, page_size()), cn_bits_u64_divide(H_cn->pool->range_end, page_size()), p_cn));
  update_cn_error_message_info("/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), H.pool.range_start / page_size(), H.pool.range_end / page_size(), p); @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1458:24-60 (cursor: 1458:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap35_cn, p_cn);
  cn_bits_u8* p_order_cn = ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->order;
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->refcount, convert_to_cn_bits_u16(0)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_pointer_equality(((struct list_head_cn*) cn_map_get_struct_list_head_cn(H_cn->APs, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->prev, cn_array_shift(cn_member_shift(pool_cn, hyp_pool, free_area), sizeof(struct list_head), p_order_cn)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u8_le(order_cn, p_order_cn));
  update_cn_error_message_info("/*@ requires (H.APs[p_i]).prev == array_shift<struct list_head>(&(pool->free_area), p_order); @*/\n                                           ~~~~~~~~~~~~~^~ ./driver.pp.c:1462:44-59 (cursor: 1462:57)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_bits_u8_equality(p_order_cn, hyp_no_order())));
  update_cn_error_message_info("/*@ requires order <= p_order; p_order != (hyp_no_order ()); @*/\n             ~~~~~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:1463:14-39 (cursor: 1463:27)");
  update_cn_error_message_info(NULL);
  cn_assert(order_aligned(p_i_cn, order_cn));
  update_cn_error_message_info("/*@ requires order_aligned(p_i, order); @*/\n                                                 ~~~~~~~~~^~ ./driver.pp.c:1464:50-61 (cursor: 1464:59)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(H_cn->pool->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = H.pool.range_start / (page_size()); @*/\n                                            ~~~~~~~~~^~ ./driver.pp.c:1465:45-56 (cursor: 1465:54)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(H_cn->pool->range_end, page_size());
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  c_add_local_to_ghost_state((uintptr_t) &order, sizeof(unsigned char));
  
    /* struct hyp_page *buddy; */
    struct hyp_page *buddy = ((void *)0);
c_add_local_to_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));

    page_remove_from_list_pool(CN_LOAD(pool), CN_LOAD(p));
    /*CN*/
    /*CN*/
    /*while (p->order > order)*/
    /*CN*/while (1)
    /*@ inv let vmemmap_l = __hyp_vmemmap; @*/
    /*@ inv take H_I = Hyp_pool_ex1(pool, vmemmap_l, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/
    /*@ inv H_I.pool == {free_area: H_I.pool.free_area, ..H.pool}; @*/
    /*@ inv {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
    /*@ inv order_aligned(p_i, order); @*/
    /*@ inv let V_I = H_I.vmemmap; @*/
    /*@ inv V_I[p_i].refcount == 0u16; @*/
    /*@ inv let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, p_i * page_size()); @*/
    /*@ inv let i_p_order = V_I[p_i].order; @*/
    /*@ inv take ZI = ZeroPage(virt, true, i_p_order); @*/
    /*@ inv order <= i_p_order; i_p_order != hyp_no_order (); i_p_order < (max_order ()); @*/
    /*@ inv {p} unchanged; {pool} unchanged; {order} unchanged; @*/
    {
        /*CN*/
        /*CN*/if (!(CN_LOAD(CN_LOAD(p)->order) > CN_LOAD(order))) break;
        /*
         * The buddy of order n - 1 currently has HYP_NO_ORDER as it
         * is covered by a higher-level page (whose head is @p). Use
         * __find_buddy_nocheck() to find it and inject it in the
         * free_list[n - 1], effectively splitting @p in half.
         */
        /*CN*/
        /*CN*/
        /*CN*/
        /*CN*/
        /*CN*/
        CN_POSTFIX(CN_LOAD(p)->order, --);
        CN_STORE(buddy, __find_buddy_nocheck(CN_LOAD(pool), CN_LOAD(p), CN_LOAD(CN_LOAD(p)->order)));
        /*CN*/
        /*CN*/
        CN_STORE(CN_LOAD(buddy)->order, CN_LOAD(CN_LOAD(p)->order));
        /*CN*/
        /*CN*/
        page_add_to_list_pool_ex1(CN_LOAD(pool), CN_LOAD(buddy), &CN_LOAD(pool)->free_area[CN_LOAD(CN_LOAD(buddy)->order)], CN_LOAD(p));
    }
    /*CN*/
    { __cn_ret = CN_LOAD(p); 
c_remove_local_from_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &buddy, sizeof(struct hyp_page*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

  c_remove_local_from_ghost_state((uintptr_t) &order, sizeof(unsigned char));

{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap36_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset38_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr26_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires let end_i = H.pool.range_end / page_size(); @*/\n                 ^./driver.pp.c:1466:18:");
  struct Hyp_pool_ex1_record* H2_cn = Hyp_pool_ex1(pool_cn, O___hyp_vmemmap36_cn, O_cn_virt_ptr26_cn, O_hyp_physvirt_offset38_cn, p_i_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/\n                                                                          ~~~~~~~~~^~ ./driver.pp.c:1467:75-86 (cursor: 1467:84)");
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); @*/\n                       ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1467:24-87 (cursor: 1467:34)");
  cn_pointer* virt_cn = cn__hyp_va(O_cn_virt_ptr26_cn, O_hyp_physvirt_offset38_cn, cn_bits_u64_multiply(p_i_cn, page_size()));
  update_cn_error_message_info("/*@ ensures let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, p_i * page_size()); @*/\n                 ^./driver.pp.c:1468:18:");
  ZeroPage(virt_cn, convert_to_cn_bool(true), order_cn, PUT);
  update_cn_error_message_info("/*@ ensures take ZR = ZeroPage(virt, true, order); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1469:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap36_cn, O___hyp_vmemmap35_cn));
  update_cn_error_message_info("/*@ ensures take ZR = ZeroPage(virt, true, order); @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1469:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset38_cn, O_hyp_physvirt_offset37_cn));
  struct hyp_pool_cn* a_11207 = alloc(sizeof(struct hyp_pool_cn));
  a_11207->free_area = H2_cn->pool->free_area;
  a_11207->range_start = H_cn->pool->range_start;
  a_11207->range_end = H_cn->pool->range_end;
  a_11207->max_order = H_cn->pool->max_order;
  update_cn_error_message_info("/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1470:13-67");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, a_11207));
  update_cn_error_message_info("/*@ ensures H2.pool == {free_area: (H2.pool).free_area, ..H.pool}; @*/\n            ^~~~~~~~~~~~ ./driver.pp.c:1471:13-25");
  cn_assert(cn_pointer_equality(return_cn, p_cn));
  struct hyp_page_cn* p_page_cn = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H2_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn));
  update_cn_error_message_info("/*@ ensures let p_page = H2.vmemmap[p_i]; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1473:13-37");
  cn_assert(cn_bits_u16_equality(p_page_cn->refcount, convert_to_cn_bits_u16(0)));
  update_cn_error_message_info("/*@ ensures let p_page = H2.vmemmap[p_i]; @*/\n                                     ^~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1473:38-60");
  cn_assert(cn_bits_u8_equality(p_page_cn->order, order_cn));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
static void __hyp_put_page(struct hyp_pool *pool, struct hyp_page *p)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_ptr; @*/
/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
/*@ requires let phys = p_i * page_size(); @*/
/*@ requires let start_i = H.pool.range_start / (page_size()); @*/
/*@ requires let end_i = H.pool.range_end / page_size(); @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end; @*/
/*@ requires let refcount = (H.vmemmap[p_i]).refcount; @*/
/*@ requires cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); @*/
/*@ requires refcount > 0u16; @*/
/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/
/*@ requires take P = Page(virt, (refcount == 1u16), H.vmemmap[p_i].order); @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/
/*@ ensures H2.pool == {free_area:H2.pool.free_area, .. H.pool}; @*/
/*@ ensures each (u64 i; p_i < i && i < end_i){(H.vmemmap[i].refcount == 0u16) || (H2.vmemmap[i] == H.vmemmap[i])}; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* p_cn = convert_to_cn_pointer(p);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset40_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap38_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr28_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0)));
  update_cn_error_message_info("/*@ requires (alloc_id) __hyp_vmemmap == (alloc_id) p; @*/\n                  ^./driver.pp.c:1523:19:");
  struct Hyp_pool_record* H_cn = Hyp_pool(pool_cn, O___hyp_vmemmap38_cn, O_cn_virt_ptr28_cn, O_hyp_physvirt_offset40_cn, GET);
  update_cn_error_message_info("/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                       ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1524:24-60 (cursor: 1524:42)");
  cn_bits_u64* p_i_cn = cn_hyp_page_to_pfn(O___hyp_vmemmap38_cn, p_cn);
  update_cn_error_message_info("/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/\n                              ~~~~~~~~~^~ ./driver.pp.c:1525:31-42 (cursor: 1525:40)");
  cn_bits_u64* phys_cn = cn_bits_u64_multiply(p_i_cn, page_size());
  update_cn_error_message_info("/*@ requires let phys = p_i * page_size(); @*/\n                                                 ~~~~~~~~~^~ ./driver.pp.c:1526:50-61 (cursor: 1526:59)");
  cn_bits_u64* start_i_cn = cn_bits_u64_divide(H_cn->pool->range_start, page_size());
  update_cn_error_message_info("/*@ requires let start_i = H.pool.range_start / (page_size()); @*/\n                                            ~~~~~~~~~^~ ./driver.pp.c:1527:45-56 (cursor: 1527:54)");
  cn_bits_u64* end_i_cn = cn_bits_u64_divide(H_cn->pool->range_end, page_size());
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(H_cn->pool->range_start, phys_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(phys_cn, H_cn->pool->range_end));
  cn_bits_u16* refcount_cn = ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->refcount;
  update_cn_error_message_info("/*@ requires let refcount = (H.vmemmap[p_i]).refcount; @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1530:14-92 (cursor: 1530:25)");
  update_cn_error_message_info(NULL);
  cn_assert(cellPointer(O___hyp_vmemmap38_cn, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))), start_i_cn, end_i_cn, p_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_lt(convert_to_cn_bits_u16(0), refcount_cn));
  update_cn_error_message_info("/*@ requires refcount > 0u16; @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1532:25-75 (cursor: 1532:35)");
  cn_pointer* virt_cn = cn__hyp_va(O_cn_virt_ptr28_cn, O_hyp_physvirt_offset40_cn, phys_cn);
  update_cn_error_message_info("/*@ requires let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); @*/\n                  ^./driver.pp.c:1533:19:");
  Page(virt_cn, cn_bits_u16_equality(refcount_cn, convert_to_cn_bits_u16(1)), ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(p_i_cn)))->order, GET);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
  
    /*CN*/
    /*CN*/
    /*CN*/
    if (hyp_page_ref_dec_and_test(CN_LOAD(p))) {
        __hyp_attach_page(CN_LOAD(pool), CN_LOAD(p));
    }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

{
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset41_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap39_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr29_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires take P = Page(virt, (refcount == 1u16), H.vmemmap[p_i].order); @*/\n                 ^./driver.pp.c:1534:18:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, O___hyp_vmemmap39_cn, O_cn_virt_ptr29_cn, O_hyp_physvirt_offset41_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1535:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset41_cn, O_hyp_physvirt_offset40_cn));
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                                             ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1535:46-72");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap39_cn, O___hyp_vmemmap38_cn));
  struct hyp_pool_cn* a_11425 = alloc(sizeof(struct hyp_pool_cn));
  a_11425->free_area = H2_cn->pool->free_area;
  a_11425->range_start = H_cn->pool->range_start;
  a_11425->range_end = H_cn->pool->range_end;
  a_11425->max_order = H_cn->pool->max_order;
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1536:13-65");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, a_11425));
  cn_bool* a_11473 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(cn_bits_u64_add(p_i_cn, convert_to_cn_bits_u64(1)));
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_lt(p_i_cn, i), cn_bits_u64_lt(i, end_i_cn)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        a_11473 = cn_bool_and(a_11473, cn_bool_or(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), struct_hyp_page_cn_equality((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H2_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(i)), (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(i)))));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info("/*@ ensures H2.pool == {free_area:H2.pool.free_area, .. H.pool}; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1537:13-116");
  cn_assert(a_11473);
  ghost_stack_depth_decr();
}
;
}
/*
 * Changes to the buddy tree and page refcounts must be done with the hyp_pool
 * lock held. If a refcount change requires an update to the buddy tree (e.g.
 * hyp_put_page()), both operations must be done within the same critical
 * section to guarantee transient states (e.g. a page with null refcount but
 * not yet attached to a free list) can't be observed by well-behaved readers.
 */
void hyp_put_page(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_ptr; @*/
/*@ requires (alloc_id) addr == (alloc_id) cn_virt_ptr; @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end; @*/
/*@ requires (mod(phys,page_size())) == 0u64; addr != NULL; @*/
/*@ requires let page_i = phys / page_size(); @*/
/*@ requires let refcount = (H.vmemmap[page_i]).refcount; @*/
/*@ requires refcount > 0u16; @*/
/*@ requires take P = Page(addr, (refcount == 1u16), H.vmemmap[page_i].order); @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area,.. H.pool}; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* addr_cn = convert_to_cn_pointer(addr);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset11_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap9_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr5_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0)));
  update_cn_error_message_info("/*@ requires (alloc_id) addr == (alloc_id) cn_virt_ptr; @*/\n                  ^./driver.pp.c:1556:19:");
  struct Hyp_pool_record* H_cn = Hyp_pool(pool_cn, O___hyp_vmemmap9_cn, O_cn_virt_ptr5_cn, O_hyp_physvirt_offset11_cn, GET);
  update_cn_error_message_info("/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1557:25-62 (cursor: 1557:35)");
  cn_bits_u64* phys_cn = cn__hyp_pa(O_hyp_physvirt_offset11_cn, addr_cn);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(H_cn->pool->range_start, phys_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(phys_cn, H_cn->pool->range_end));
  update_cn_error_message_info("/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end; @*/\n                       ~~~~~~~~~^~ ./driver.pp.c:1559:24-35 (cursor: 1559:33)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_equality(cn_bits_u64_mod(phys_cn, page_size()), convert_to_cn_bits_u64(0)));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bool_not(cn_pointer_equality(addr_cn, convert_to_cn_pointer(NULL))));
  update_cn_error_message_info("/*@ requires (mod(phys,page_size())) == 0u64; addr != NULL; @*/\n                                 ~~~~~~~~~^~ ./driver.pp.c:1560:34-45 (cursor: 1560:43)");
  cn_bits_u64* page_i_cn = cn_bits_u64_divide(phys_cn, page_size());
  cn_bits_u16* refcount_cn = ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(page_i_cn)))->refcount;
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_lt(convert_to_cn_bits_u16(0), refcount_cn));
  update_cn_error_message_info("/*@ requires refcount > 0u16; @*/\n                  ^./driver.pp.c:1563:19:");
  Page(addr_cn, cn_bits_u16_equality(refcount_cn, convert_to_cn_bits_u16(1)), ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(page_i_cn)))->order, GET);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &addr, sizeof(void*));
  
    struct hyp_page *p = (&((struct hyp_page *)CN_LOAD(__hyp_vmemmap))[((((phys_addr_t)CN_LOAD((addr)) + CN_LOAD(hyp_physvirt_offset))) >> 12)]);
c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

    /* hyp_spin_lock(&pool->lock); */
    __hyp_put_page(CN_LOAD(pool), CN_LOAD(p));
    /* hyp_spin_unlock(&pool->lock); */

c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &addr, sizeof(void*));

{
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset12_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap10_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr6_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires take P = Page(addr, (refcount == 1u16), H.vmemmap[page_i].order); @*/\n                 ^./driver.pp.c:1564:18:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, O___hyp_vmemmap10_cn, O_cn_virt_ptr6_cn, O_hyp_physvirt_offset12_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1565:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset12_cn, O_hyp_physvirt_offset11_cn));
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                                             ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1565:46-72");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap10_cn, O___hyp_vmemmap9_cn));
  struct hyp_pool_cn* a_7977 = alloc(sizeof(struct hyp_pool_cn));
  a_7977->free_area = H2_cn->pool->free_area;
  a_7977->range_start = H_cn->pool->range_start;
  a_7977->range_end = H_cn->pool->range_end;
  a_7977->max_order = H_cn->pool->max_order;
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1566:13-65");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, a_7977));
  ghost_stack_depth_decr();
}
;
}
/* void hyp_get_page(void *addr) */
void hyp_get_page(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_ptr; @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/
/*@ requires let page_i = phys / page_size(); @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end; @*/
/*@ requires (H.vmemmap[page_i]).refcount > 0u16; @*/
/*@ requires (H.vmemmap[page_i]).refcount <= shift_left(1u16,16u16) - 2u16; @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/
/*@ ensures H2.pool == H.pool; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_pointer* addr_cn = convert_to_cn_pointer(addr);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset9_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap7_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr3_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info("/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_ptr; @*/\n                  ^./driver.pp.c:1576:19:");
  struct Hyp_pool_record* H_cn = Hyp_pool(pool_cn, O___hyp_vmemmap7_cn, O_cn_virt_ptr3_cn, O_hyp_physvirt_offset9_cn, GET);
  update_cn_error_message_info("/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                        ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1577:25-62 (cursor: 1577:35)");
  cn_bits_u64* phys_cn = cn__hyp_pa(O_hyp_physvirt_offset9_cn, addr_cn);
  update_cn_error_message_info("/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/\n                                 ~~~~~~~~~^~ ./driver.pp.c:1578:34-45 (cursor: 1578:43)");
  cn_bits_u64* page_i_cn = cn_bits_u64_divide(phys_cn, page_size());
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(H_cn->pool->range_start, phys_cn));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_lt(phys_cn, H_cn->pool->range_end));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_lt(convert_to_cn_bits_u16(0), ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(page_i_cn)))->refcount));
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u16_le(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(H_cn->vmemmap, cast_cn_bits_u64_to_cn_integer(page_i_cn)))->refcount, cn_bits_u16_sub(cn_bits_u16_shift_left(convert_to_cn_bits_u16(1), convert_to_cn_bits_u16(16)), convert_to_cn_bits_u16(2))));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &addr, sizeof(void*));
  
    struct hyp_page *p = (&((struct hyp_page *)CN_LOAD(__hyp_vmemmap))[((((phys_addr_t)CN_LOAD((addr)) + CN_LOAD(hyp_physvirt_offset))) >> 12)]);
c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

    /* hyp_spin_lock(&pool->lock); */
    /*CN*/
    /*CN*/
    hyp_page_ref_inc(CN_LOAD(p));
    /* hyp_spin_unlock(&pool->lock); */

c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &addr, sizeof(void*));

{
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset10_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap8_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr4_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires (H.vmemmap[page_i]).refcount <= shift_left(1u16,16u16) - 2u16; @*/\n                 ^./driver.pp.c:1582:18:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, O___hyp_vmemmap8_cn, O_cn_virt_ptr4_cn, O_hyp_physvirt_offset10_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1583:13-45");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset10_cn, O_hyp_physvirt_offset9_cn));
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n                                             ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1583:46-72");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap8_cn, O___hyp_vmemmap7_cn));
  update_cn_error_message_info("/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; @*/\n            ^~~~~~~~~~~~~~~~~~ ./driver.pp.c:1584:13-31");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, H_cn->pool));
  ghost_stack_depth_decr();
}
;
}
// void hyp_split_page(struct hyp_page *p)
// {
//     u8 order = p->order;
//     unsigned int i;
//
//     p->order = 0;
//     for (i = 1; i < (1 << order); i++) {
//         struct hyp_page *tail = p + i;
//
//         tail->order = 0;
//         hyp_set_page_refcounted(tail);
//     }
// }
void *hyp_alloc_pages(struct hyp_pool *pool, u8 order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_ptr; @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ requires 0i64 <= hyp_physvirt_offset; @*/ /* FIXME from node_to_page, suspicious */
/*@ ensures  take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset);
             take ZR = ZeroPage(return, (return != NULL), order);
             {__hyp_vmemmap} unchanged;
             {hyp_physvirt_offset} unchanged;
             H2.pool == {free_area: H2.pool.free_area, ..H.pool}; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  void* __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_bits_u8* order_cn = convert_to_cn_bits_u8(order);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset6_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap4_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr0_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info("/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_ptr; @*/\n                  ^./driver.pp.c:1608:19:");
  struct Hyp_pool_record* H_cn = Hyp_pool(pool_cn, O___hyp_vmemmap4_cn, O_cn_virt_ptr0_cn, O_hyp_physvirt_offset6_cn, GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_i64_le(convert_to_cn_bits_i64(0), O_hyp_physvirt_offset6_cn));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &order, sizeof(unsigned char));
  
    struct hyp_page *p = ((void *)0);
c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));
 /* struct hyp_page *p; */
    u8 i = CN_LOAD(order);
c_add_local_to_ghost_state((uintptr_t) &i, sizeof(unsigned char));

    /* ----- hyp_spin_lock(&pool- >lock); */
    /* Look for a high-enough-order page */
    while /*CN(i < pool->max_order && list_empty(&pool->free_area[i]))*/ (1)
        /*@ inv take H_I = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset);
            H_I.vmemmap == H.vmemmap; H_I.pool == H.pool;
            order <= i; H.pool.max_order <= 11u8;
            {pool} unchanged; {order} unchanged;
            {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
        /*CN*/{
            /*CN*/ 
            /*CN*/ 
            /*CN*/if (!(CN_LOAD(i) < CN_LOAD(CN_LOAD(pool)->max_order) && list_empty(&CN_LOAD(pool)->free_area[CN_LOAD(i)]))) break;
            CN_POSTFIX(i, ++);
        /*CN*/}
    if (CN_LOAD(i) >= CN_LOAD(CN_LOAD(pool)->max_order)) {
        /* ----- hyp_spin_unlock(&pool->lock); */
    //cn_print_nr_u64(555555, 555555);
        { __cn_ret = ((void *)0); 
c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &i, sizeof(unsigned char));
goto __cn_epilogue; }
    }
    /*CN*/
    /*CN*/
    /* Extract it from the tree at the right order */
    CN_STORE(p, node_to_page(CN_LOAD(CN_LOAD(pool)->free_area[CN_LOAD(i)].next)));
    // p = hyp_virt_to_page(pool->free_area[i].next);
    /*CN*/
                /*CN*/ 
    /*CN*/
    CN_STORE(p, __hyp_extract_page(CN_LOAD(pool), CN_LOAD(p), CN_LOAD(order)));
    /* ----- hyp_spin_unlock(&pool->lock); */
    /*CN*/
    hyp_set_page_refcounted(CN_LOAD(p));
    /* ----- hyp_spin_unlock(&pool->lock); */
    //cn_print_nr_u64(666666, 666666);
    { __cn_ret = copy_alloc_id((((phys_addr_t)(((phys_addr_t)(((hyp_page_to_pfn(CN_LOAD(p)))) << 12))) - CN_LOAD(hyp_physvirt_offset))), CN_LOAD((cn_virt_ptr))); 
c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &i, sizeof(unsigned char));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &i, sizeof(unsigned char));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &order, sizeof(unsigned char));

{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset7_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap5_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr1_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ requires 0i64 <= hyp_physvirt_offset; @*/ /* FIXME from node_to_page, suspicious */\n                  ^./driver.pp.c:1610:19:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, O___hyp_vmemmap5_cn, O_cn_virt_ptr1_cn, O_hyp_physvirt_offset7_cn, PUT);
  update_cn_error_message_info("/*@ ensures  take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset);\n                  ^./driver.pp.c:1611:19:");
  ZeroPage(return_cn, cn_bool_not(cn_pointer_equality(return_cn, convert_to_cn_pointer(NULL))), order_cn, PUT);
  update_cn_error_message_info("             take ZR = ZeroPage(return, (return != NULL), order);\n             ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1612:14-40");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap5_cn, O___hyp_vmemmap4_cn));
  update_cn_error_message_info("             {__hyp_vmemmap} unchanged;\n             ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1613:14-46");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset7_cn, O_hyp_physvirt_offset6_cn));
  struct hyp_pool_cn* a_7690 = alloc(sizeof(struct hyp_pool_cn));
  a_7690->free_area = H2_cn->pool->free_area;
  a_7690->range_start = H_cn->pool->range_start;
  a_7690->range_end = H_cn->pool->range_end;
  a_7690->max_order = H_cn->pool->max_order;
  update_cn_error_message_info("             {hyp_physvirt_offset} unchanged;\n             ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1614:14-66");
  cn_assert(struct_hyp_pool_cn_equality(H2_cn->pool, a_7690));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
/* SPDX-License-Identifier: GPL-2.0 */
//#ifndef __ASM_GENERIC_GETORDER_H
//#define __ASM_GENERIC_GETORDER_H
//#ifndef __ASSEMBLY__
//#include <linux/compiler.h>
//#include <linux/log2.h>
/**
 * get_order - Determine the allocation order of a memory size
 * @size: The size for which to get the order
 *
 * Determine the allocation order of a particular sized block of memory.  This
 * is on a logarithmic scale, where:
 *
 *    0 -> 2^0 * PAGE_SIZE and below
 *    1 -> 2^1 * PAGE_SIZE to 2^0 * PAGE_SIZE + 1
 *    2 -> 2^2 * PAGE_SIZE to 2^1 * PAGE_SIZE + 1
 *    3 -> 2^3 * PAGE_SIZE to 2^2 * PAGE_SIZE + 1
 *    4 -> 2^4 * PAGE_SIZE to 2^3 * PAGE_SIZE + 1
 *    ...
 *
 * The order returned is used to find the smallest allocation granule required
 * to hold an object of the specified size.
 *
 * The result is undefined if the size is 0.
 */
// CP: adding string.h include
//#include <string.h>
long fls64(long x)
{
  /* EXECUTABLE CN PRECONDITION */
  signed long __cn_ret;
  ghost_stack_depth_incr();
  cn_bits_i64* x_cn = convert_to_cn_bits_i64(x);
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &x, sizeof(signed long));
  
  long flsl(long);
  { __cn_ret = flsl(CN_LOAD(x)); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &x, sizeof(signed long));

{
  cn_bits_i64* return_cn = convert_to_cn_bits_i64(__cn_ret);
  ghost_stack_depth_decr();
}

return __cn_ret;

}
//#define fls64 flsl
static /*__always_inline __attribute_const__*/ int get_order(unsigned long size)
/*@ trusted; @*/
/*@ requires size >= page_size(); @*/
/*@ ensures return == (i32) get_order_uf(size); @*/
/*@ ensures return > 0i32; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret;
  ghost_stack_depth_incr();
  cn_bits_u64* size_cn = convert_to_cn_bits_u64(size);
  update_cn_error_message_info("/*@ trusted; @*/\n                     ~~~~~~~~~^~ ./driver.pp.c:1688:22-33 (cursor: 1688:31)");
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u64_le(page_size(), size_cn));
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &size, sizeof(unsigned long));
  
/*    if (__builtin_constant_p(size)) {
        if (!size)
            return BITS_PER_LONG - PAGE_SHIFT;

        if (size < (1UL << PAGE_SHIFT))
            return 0;

        return ilog2((size) - 1) - PAGE_SHIFT + 1;
    }
*/
    CN_POSTFIX(size, --);
    CN_STORE_OP(size,>>,12);
    { __cn_ret = fls64(CN_LOAD(size)); goto __cn_epilogue; }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &size, sizeof(unsigned long));

{
  cn_bits_i32* return_cn = convert_to_cn_bits_i32(__cn_ret);
  update_cn_error_message_info("/*@ requires size >= page_size(); @*/\n                            ~~~~~~~~~~~~^~~~~~ ./driver.pp.c:1689:29-47 (cursor: 1689:41)");
  update_cn_error_message_info("/*@ requires size >= page_size(); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1689:13-48");
  cn_assert(cn_bits_i32_equality(return_cn, cast_cn_bits_u8_to_cn_bits_i32(get_order_uf(size_cn))));
  update_cn_error_message_info("/*@ ensures return == (i32) get_order_uf(size); @*/\n            ^~~~~~~~~~~~~~ ./driver.pp.c:1690:13-27");
  cn_assert(cn_bits_i32_lt(convert_to_cn_bits_i32(0), return_cn));
  ghost_stack_depth_decr();
}

return __cn_ret;

}
//#endif    /* __ASSEMBLY__ */
//#endif    /* __ASM_GENERIC_GETORDER_H */

int hyp_pool_init(struct hyp_pool *pool, u64 pfn, unsigned int nr_pages,
          unsigned int reserved_pages)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; @*/
/*@ requires nr_pages > 0u32; @*/
/*@ requires take O = Owned<struct hyp_pool>(pool); @*/
/*@ requires let start_i = pfn; let start = start_i * page_size(); @*/
/*@ requires let end_i = start_i + ((u64) nr_pages); let end = end_i * page_size(); @*/
/*@ requires reserved_pages < nr_pages; @*/
/* The hyp_pool_wf below does not mention the free area. So the
   hyp_pool_wf constraint is just a short-hand for asking start,
   end, and others to have sensible values. */
/*@ requires let poolv = {range_start: start, range_end: end, max_order: 11u8, ..*pool}; @*/
/*@ requires hyp_pool_wf(pool, poolv, __hyp_vmemmap, hyp_physvirt_offset); @*/
/*@ requires take V = each (u64 i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; @*/
/*@ requires let ptr_phys_0 = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, 0u64); @*/
/*@ requires take P = each (u64 i; start_i + ((u64) reserved_pages) <= i && i < end_i)
  { Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), true, 0u8) }; @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
/*@ ensures (H2.pool).range_start == start; @*/
/*@ ensures (H2.pool).range_end == end; @*/
/*@ ensures (H2.pool).max_order <= 11u8; @*/
{
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret;
  ghost_stack_depth_incr();
  cn_pointer* pool_cn = convert_to_cn_pointer(pool);
  cn_bits_u64* pfn_cn = convert_to_cn_bits_u64(pfn);
  cn_bits_u32* nr_pages_cn = convert_to_cn_bits_u32(nr_pages);
  cn_bits_u32* reserved_pages_cn = convert_to_cn_bits_u32(reserved_pages);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap11_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset13_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr7_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u32_lt(convert_to_cn_bits_u32(0), nr_pages_cn));
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* O_cn = owned_struct_hyp_pool(pool_cn, GET);
  cn_bits_u64* start_i_cn = pfn_cn;
  update_cn_error_message_info("/*@ requires take O = Owned<struct hyp_pool>(pool); @*/\n                                                      ~~~~~~~~~^~ ./driver.pp.c:1714:55-66 (cursor: 1714:64)");
  cn_bits_u64* start_cn = cn_bits_u64_multiply(start_i_cn, page_size());
  cn_bits_u64* end_i_cn = cn_bits_u64_add(start_i_cn, cast_cn_bits_u32_to_cn_bits_u64(nr_pages_cn));
  update_cn_error_message_info("/*@ requires let start_i = pfn; let start = start_i * page_size(); @*/\n                                                                       ~~~~~~~~~^~ ./driver.pp.c:1715:72-83 (cursor: 1715:81)");
  cn_bits_u64* end_cn = cn_bits_u64_multiply(end_i_cn, page_size());
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u32_lt(reserved_pages_cn, nr_pages_cn));
  struct hyp_pool_cn* a_8056 = alloc(sizeof(struct hyp_pool_cn));
  a_8056->free_area = O_cn->free_area;
  a_8056->range_start = start_cn;
  a_8056->range_end = O_cn->range_end;
  a_8056->max_order = O_cn->max_order;
  struct hyp_pool_cn* a_8059 = alloc(sizeof(struct hyp_pool_cn));
  a_8059->free_area = a_8056->free_area;
  a_8059->range_start = a_8056->range_start;
  a_8059->range_end = end_cn;
  a_8059->max_order = a_8056->max_order;
  struct hyp_pool_cn* a_8064 = alloc(sizeof(struct hyp_pool_cn));
  a_8064->free_area = a_8059->free_area;
  a_8064->range_start = a_8059->range_start;
  a_8064->range_end = a_8059->range_end;
  a_8064->max_order = convert_to_cn_bits_u8(11);
  struct hyp_pool_cn* poolv_cn = a_8064;
  update_cn_error_message_info("/*@ requires let poolv = {range_start: start, range_end: end, max_order: 11u8, ..*pool}; @*/\n             ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1721:14-74 (cursor: 1721:25)");
  update_cn_error_message_info(NULL);
  cn_assert(hyp_pool_wf(pool_cn, poolv_cn, O___hyp_vmemmap11_cn, O_hyp_physvirt_offset13_cn));
  update_cn_error_message_info("unknown location");
  cn_map* V_cn = map_create();
  {
  cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i_cn);
  while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i_cn, i), cn_bits_u64_lt(i, end_i_cn)))) {
    if (convert_from_cn_bool(convert_to_cn_bool(true))) {
      cn_pointer* a_8094 = cn_pointer_add_cn_bits_u64(O___hyp_vmemmap11_cn, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
      cn_map_set(V_cn, cast_cn_bits_u64_to_cn_integer(i), owned_struct_hyp_page(a_8094, GET));
    }
    else {
      ;
    }
    cn_bits_u64_increment(i);
  }
}
  update_cn_error_message_info("/*@ requires take V = each (u64 i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; @*/\n                              ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1723:31-81 (cursor: 1723:41)");
  cn_pointer* ptr_phys_0_cn = cn__hyp_va(O_cn_virt_ptr7_cn, O_hyp_physvirt_offset13_cn, convert_to_cn_bits_u64(0));
  update_cn_error_message_info("/*@ requires let ptr_phys_0 = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, 0u64); @*/\n                  ^./driver.pp.c:1724:19:");
  {
  cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(cn_bits_u64_add(start_i_cn, cast_cn_bits_u32_to_cn_bits_u64(reserved_pages_cn)));
  while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(cn_bits_u64_add(start_i_cn, cast_cn_bits_u32_to_cn_bits_u64(reserved_pages_cn)), i), cn_bits_u64_lt(i, end_i_cn)))) {
    if (convert_from_cn_bool(convert_to_cn_bool(true))) {
      cn_pointer* a_8148 = cn_pointer_add_cn_bits_u64(ptr_phys_0_cn, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(char[4096])))));
      Page(a_8148, convert_to_cn_bool(true), convert_to_cn_bits_u8(0), GET);
    }
    else {
      ;
    }
    cn_bits_u64_increment(i);
  }
}
  
	/* C OWNERSHIP */

  c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
  c_add_local_to_ghost_state((uintptr_t) &pfn, sizeof(unsigned long long));
  c_add_local_to_ghost_state((uintptr_t) &nr_pages, sizeof(unsigned int));
  c_add_local_to_ghost_state((uintptr_t) &reserved_pages, sizeof(unsigned int));
  
    phys_addr_t phys = ((phys_addr_t)(CN_LOAD((pfn)) << 12));
c_add_local_to_ghost_state((uintptr_t) &phys, sizeof(unsigned long long));

    struct hyp_page *p = ((void *)0);
c_add_local_to_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));

    /* struct hyp_page *p; */
    int i;
c_add_local_to_ghost_state((uintptr_t) &i, sizeof(signed int));

    /* hyp_spin_lock_init(&pool->lock); */
    CN_STORE(CN_LOAD(pool)->max_order, ((11) < (get_order((CN_LOAD(nr_pages) + 1) << 12)) ? (11) : (get_order((CN_LOAD(nr_pages) + 1) << 12))));
    ((void) 0);
    for (CN_STORE(i, 0); CN_LOAD(i) < CN_LOAD(CN_LOAD(pool)->max_order); CN_POSTFIX(i, ++))
    /*@ inv take OI = Owned(pool); @*/
    /*@ inv take V2 = each (u64 j; start_i <= j && j < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, j))}; @*/
    /*@ inv take PI = each (u64 j; start_i + ((u64) reserved_pages) <= j && j < end_i){ Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, j), true, 0u8) }; @*/
    /*@ inv each(u64 j; j < (u64) i){((*pool).free_area[j]).prev == array_shift<struct list_head>(pool, j) }; @*/
    /*@ inv each(u64 j; j < (u64) i){((*pool).free_area[j]).next == array_shift<struct list_head>(pool, j) }; @*/
    /*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged; @*/
    /*@ inv 0i32 <= i; i <= (i32) (*pool).max_order; (*pool).max_order > 0u8; (*pool).max_order <= 11u8; @*/
    /*@ inv let order = get_order_uf(((u64) nr_pages + 1u64)*(page_size())); @*/
    /*@ inv (*pool).max_order == (11u8 < order ? 11u8 : order); @*/
    /*@ inv phys == pfn * page_size(); @*/
    {
        /*CN*/ 
        INIT_LIST_HEAD(&CN_LOAD(pool)->free_area[CN_LOAD(i)]);
    }
    CN_STORE(CN_LOAD(pool)->range_start, CN_LOAD(phys));
    CN_STORE(CN_LOAD(pool)->range_end, CN_LOAD(phys) + (CN_LOAD(nr_pages) << 12));
    /* Init the vmemmap portion */
    CN_STORE(p, (&((struct hyp_page *)CN_LOAD(__hyp_vmemmap))[(CN_LOAD((phys)) >> 12)]));
    for (CN_STORE(i, 0); CN_LOAD(i) < CN_LOAD(nr_pages); CN_POSTFIX(i, ++))
    /*@ inv take OI2 = Owned(pool); @*/
    /*@ inv take V3 = each (u64 j; start_i <= j && j < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, j)) }; @*/
    /*@ inv take PI2 = each (u64 j; start_i + ((u64) reserved_pages) <= j && j < end_i){ Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, j), true, 0u8) }; @*/
    /*@ inv each(u8 j; j < (*pool).max_order){((*pool).free_area[(u64) j]).prev == array_shift<struct list_head>(pool, j)}; @*/
    /*@ inv each(u8 j; j < ((*pool).max_order)){((*pool).free_area[(u64) j]).next == array_shift<struct list_head>(pool, j)}; @*/
    /*@ inv each (u64 j; start_i <= j && j < start_i + (u64) i){init_vmemmap_page(j, V3, pool, *pool)}; @*/
    /*@ inv 0i32 <= i; (u32) i <= nr_pages; @*/
    /*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged; @*/
    /*@ inv (*pool).range_start == start; @*/
    /*@ inv (*pool).range_end == end; @*/
    /*@ inv (*pool).max_order > 0u8; @*/
    /*@ inv (*pool).max_order <= 11u8; @*/
    /*@ inv let order = get_order_uf(((u64)nr_pages + 1u64)*(page_size())); @*/
    /*@ inv (*pool).max_order == (11u8 < order ? 11u8 : order); @*/
    /*@ inv hyp_pool_wf(pool, (*pool), __hyp_vmemmap, hyp_physvirt_offset); @*/
    /*@ inv p == array_shift<struct hyp_page>(__hyp_vmemmap, pfn); @*/
    {
        /*CN*/
        /*CN*/
        CN_STORE(CN_LOAD(p)[CN_LOAD(i)].refcount, 0); /* added for formalisation */
        CN_STORE(CN_LOAD(p)[CN_LOAD(i)].order, 0); /* added for formalisation */
        hyp_set_page_refcounted(&CN_LOAD(p)[CN_LOAD(i)]);
        /*CN*/
        /*CN*/
    }
    /*CN*/
    /* Attach the unused pages to the buddy tree */
    for (CN_STORE(i, CN_LOAD(reserved_pages)); CN_LOAD(i) < CN_LOAD(nr_pages); CN_POSTFIX(i, ++))
    /*@ inv take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/
    /*@ inv i >= 0i32; @*/
    /*@ inv take PI3 = each(u64 j; start_i + ((u64) i) <= j && j < end_i){ Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, j), true, 0u8) }; @*/
    /*@ inv each(u64 j; start_i + (u64) i <= j && j < end_i){H.vmemmap[j].order == 0u8}; @*/
    /*@ inv each(u64 j; start_i + (u64) i <= j && j < end_i){H.vmemmap[j].refcount == 1u16}; @*/
    /*@ inv (H.pool).range_start == start; @*/
    /*@ inv (H.pool).range_end == end; @*/
    /*@ inv p == array_shift<struct hyp_page>(__hyp_vmemmap, pfn); @*/
    /*@ inv reserved_pages <= (u32) i; (u32) i <= nr_pages; @*/
    /*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged; @*/
    /*@ inv (H.pool).range_start == start; @*/
    /*@ inv (H.pool).range_end == end; @*/
    /*@ inv (H.pool).max_order <= 11u8; @*/
    {
        /*CN*/
        // p[i].refcount = 0; /* added for formalisation */
        /*CN*/ 
        __hyp_put_page(CN_LOAD(pool), &CN_LOAD(p)[CN_LOAD(i)]);
    }
    ((void) 0);
    { __cn_ret = 0; 
c_remove_local_from_ghost_state((uintptr_t) &phys, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &i, sizeof(signed int));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &phys, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &p, sizeof(struct hyp_page*));


c_remove_local_from_ghost_state((uintptr_t) &i, sizeof(signed int));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  c_remove_local_from_ghost_state((uintptr_t) &pfn, sizeof(unsigned long long));

  c_remove_local_from_ghost_state((uintptr_t) &nr_pages, sizeof(unsigned int));

  c_remove_local_from_ghost_state((uintptr_t) &reserved_pages, sizeof(unsigned int));

{
  cn_bits_i32* return_cn = convert_to_cn_bits_i32(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap12_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset14_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr8_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("  { Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), true, 0u8) }; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1726:13-39");
  cn_assert(cn_pointer_equality(O___hyp_vmemmap12_cn, O___hyp_vmemmap11_cn));
  update_cn_error_message_info("  { Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), true, 0u8) }; @*/\n                                       ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1726:40-72");
  cn_assert(cn_bits_i64_equality(O_hyp_physvirt_offset14_cn, O_hyp_physvirt_offset13_cn));
  update_cn_error_message_info("/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/\n                 ^./driver.pp.c:1727:18:");
  struct Hyp_pool_record* H2_cn = Hyp_pool(pool_cn, O___hyp_vmemmap12_cn, O_cn_virt_ptr8_cn, O_hyp_physvirt_offset14_cn, PUT);
  update_cn_error_message_info("/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1728:13-44");
  cn_assert(cn_bits_u64_equality(H2_cn->pool->range_start, start_cn));
  update_cn_error_message_info("/*@ ensures (H2.pool).range_start == start; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1729:13-40");
  cn_assert(cn_bits_u64_equality(H2_cn->pool->range_end, end_cn));
  update_cn_error_message_info("/*@ ensures (H2.pool).range_end == end; @*/\n            ^~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:1730:13-41");
  cn_assert(cn_bits_u8_le(H2_cn->pool->max_order, convert_to_cn_bits_u8(11)));
  ghost_stack_depth_decr();
}

return __cn_ret;

}

void *cn_aligned_alloc(size_t align, size_t size);
void *cn_malloc(unsigned long size);
void *cn_calloc(size_t num, size_t size);
void cn_print_u64(const char *, unsigned long);
s64 hyp_physvirt_offset;
struct hyp_pool *init()
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr;
    ensures take H = Hyp_pool(return, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
@*/
{
  /* EXECUTABLE CN PRECONDITION */
  struct hyp_pool* __cn_ret;
  ghost_stack_depth_incr();
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap40_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), GET);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset42_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), GET);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr30_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), GET);
  
	/* C OWNERSHIP */

  
  CN_STORE(hyp_physvirt_offset, 0x0);
  unsigned int nr_pages = 8;
c_add_local_to_ghost_state((uintptr_t) &nr_pages, sizeof(unsigned int));

  unsigned int reserved_pages = 0;
c_add_local_to_ghost_state((uintptr_t) &reserved_pages, sizeof(unsigned int));

  u8 max_order = 10;
c_add_local_to_ghost_state((uintptr_t) &max_order, sizeof(unsigned char));

  void *start_virt = cn_aligned_alloc(((1UL) << 12), ((1UL) << 12) * CN_LOAD(nr_pages));
c_add_local_to_ghost_state((uintptr_t) &start_virt, sizeof(void*));

  phys_addr_t range_start = (phys_addr_t) ((phys_addr_t)CN_LOAD((start_virt)) + CN_LOAD(hyp_physvirt_offset));
c_add_local_to_ghost_state((uintptr_t) &range_start, sizeof(unsigned long long));

  u64 pfn = (CN_LOAD((range_start)) >> 12);
c_add_local_to_ghost_state((uintptr_t) &pfn, sizeof(unsigned long long));

  u64 npfn = 0-CN_LOAD(pfn);
c_add_local_to_ghost_state((uintptr_t) &npfn, sizeof(unsigned long long));

  u64 vmemmap_size = sizeof(struct hyp_page) * CN_LOAD(nr_pages);
c_add_local_to_ghost_state((uintptr_t) &vmemmap_size, sizeof(unsigned long long));

  void *start_of_owned_vmemmap = cn_malloc(CN_LOAD(vmemmap_size));
c_add_local_to_ghost_state((uintptr_t) &start_of_owned_vmemmap, sizeof(void*));

  CN_STORE(__hyp_vmemmap, ((struct hyp_page *) CN_LOAD(start_of_owned_vmemmap)) + CN_LOAD(npfn));
  struct hyp_pool *pool = cn_calloc(1, sizeof(struct hyp_pool));
c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  CN_STORE(CN_LOAD(pool)->range_start, CN_LOAD(range_start));
  CN_STORE(CN_LOAD(pool)->range_end, CN_LOAD(range_start) + CN_LOAD(nr_pages) * ((1UL) << 12));
  CN_STORE(CN_LOAD(pool)->max_order, CN_LOAD(max_order));
  hyp_pool_init(CN_LOAD(pool), (CN_LOAD((range_start)) >> 12), CN_LOAD(nr_pages), CN_LOAD(reserved_pages));
  { __cn_ret = CN_LOAD(pool); 
c_remove_local_from_ghost_state((uintptr_t) &nr_pages, sizeof(unsigned int));


c_remove_local_from_ghost_state((uintptr_t) &reserved_pages, sizeof(unsigned int));


c_remove_local_from_ghost_state((uintptr_t) &max_order, sizeof(unsigned char));


c_remove_local_from_ghost_state((uintptr_t) &start_virt, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &range_start, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &pfn, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &npfn, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &vmemmap_size, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &start_of_owned_vmemmap, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &nr_pages, sizeof(unsigned int));


c_remove_local_from_ghost_state((uintptr_t) &reserved_pages, sizeof(unsigned int));


c_remove_local_from_ghost_state((uintptr_t) &max_order, sizeof(unsigned char));


c_remove_local_from_ghost_state((uintptr_t) &start_virt, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &range_start, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &pfn, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &npfn, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &vmemmap_size, sizeof(unsigned long long));


c_remove_local_from_ghost_state((uintptr_t) &start_of_owned_vmemmap, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


{
  cn_pointer* return_cn = convert_to_cn_pointer(__cn_ret);
  update_cn_error_message_info("unknown location");
  cn_pointer* O___hyp_vmemmap41_cn = owned_struct_hyp_page_pointer(convert_to_cn_pointer((&__hyp_vmemmap)), PUT);
  update_cn_error_message_info("unknown location");
  cn_bits_i64* O_hyp_physvirt_offset43_cn = owned_signed_long_long(convert_to_cn_pointer((&hyp_physvirt_offset)), PUT);
  update_cn_error_message_info("unknown location");
  cn_pointer* O_cn_virt_ptr31_cn = owned_void_pointer(convert_to_cn_pointer((&cn_virt_ptr)), PUT);
  update_cn_error_message_info("/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr;\n                 ^./driver.pp.c:1817:18:");
  struct Hyp_pool_record* H_cn = Hyp_pool(return_cn, O___hyp_vmemmap41_cn, O_cn_virt_ptr31_cn, O_hyp_physvirt_offset43_cn, PUT);
  ghost_stack_depth_decr();
}

return __cn_ret;

}
/*
int main(void)
{
  struct hyp_pool *pool = init();

  void *page1 = hyp_alloc_pages(pool, 2);
  if (page1) {
    ((char *)page1)[1234] = 1;
    hyp_get_page(pool, page1);
    hyp_get_page(pool, page1);
    hyp_put_page(pool, page1);
    cn_print_nr_u64(1, 1);
  }
  else {
    cn_print_nr_u64(2, 2);
  }
  return 0;
} 
*/
int main(void)
{
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret = 0;
  initialise_ownership_ghost_state();
  initialise_ghost_stack_depth();
  c_add_local_to_ghost_state((uintptr_t) &hyp_physvirt_offset, sizeof(signed long long));
  c_add_local_to_ghost_state((uintptr_t) &__hyp_vmemmap, sizeof(struct hyp_page*));
  c_add_local_to_ghost_state((uintptr_t) &cn_virt_base, sizeof(void*));
  c_add_local_to_ghost_state((uintptr_t) &cn_virt_ptr, sizeof(void*));
  
  struct hyp_pool *pool = init();
c_add_local_to_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));

  void *page0 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page0, sizeof(void*));

  void *page1 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page1, sizeof(void*));

  void *page2 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page2, sizeof(void*));

  void *page3 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page3, sizeof(void*));

  void *page4 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page4, sizeof(void*));

  void *page5 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page5, sizeof(void*));

  void *page6 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page6, sizeof(void*));

  void *page7 = hyp_alloc_pages(CN_LOAD(pool), 0);
c_add_local_to_ghost_state((uintptr_t) &page7, sizeof(void*));

  cn_print_nr_u64 (0, CN_LOAD(page0)?1:0);
  cn_print_nr_u64 (1, CN_LOAD(page1)?1:0);
  cn_print_nr_u64 (2, CN_LOAD(page2)?1:0);
  cn_print_nr_u64 (3, CN_LOAD(page3)?1:0);
  cn_print_nr_u64 (4, CN_LOAD(page4)?1:0);
  cn_print_nr_u64 (5, CN_LOAD(page5)?1:0);
  cn_print_nr_u64 (6, CN_LOAD(page6)?1:0);
  cn_print_nr_u64 (7, CN_LOAD(page7)?1:0);
  CN_STORE(((char *)CN_LOAD(page0))[1234], 1);
  CN_STORE(((char *)CN_LOAD(page1))[1234], 1);
  CN_STORE(((char *)CN_LOAD(page2))[1234], 1);
  CN_STORE(((char *)CN_LOAD(page3))[1234], 1);
  CN_STORE(((char *)CN_LOAD(page4))[1234], 1);
  CN_STORE(((char *)CN_LOAD(page5))[1234], 1);
  CN_STORE(((char *)CN_LOAD(page6))[1234], 1);
  CN_STORE(((char *)CN_LOAD(page7))[1234], 1);
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page0));
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page1));
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page2));
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page3));
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page4));
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page5));
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page6));
  hyp_put_page(CN_LOAD(pool), CN_LOAD(page7));
  void *page = hyp_alloc_pages(CN_LOAD(pool), 2);
c_add_local_to_ghost_state((uintptr_t) &page, sizeof(void*));

  { __cn_ret = 0; 
c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));


c_remove_local_from_ghost_state((uintptr_t) &page0, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page1, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page2, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page3, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page4, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page5, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page6, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page7, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page, sizeof(void*));
goto __cn_epilogue; }

c_remove_local_from_ghost_state((uintptr_t) &pool, sizeof(struct hyp_pool*));


c_remove_local_from_ghost_state((uintptr_t) &page0, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page1, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page2, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page3, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page4, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page5, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page6, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page7, sizeof(void*));


c_remove_local_from_ghost_state((uintptr_t) &page, sizeof(void*));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  c_remove_local_from_ghost_state((uintptr_t) &hyp_physvirt_offset, sizeof(signed long long));

  c_remove_local_from_ghost_state((uintptr_t) &__hyp_vmemmap, sizeof(struct hyp_page*));

  c_remove_local_from_ghost_state((uintptr_t) &cn_virt_base, sizeof(void*));

  c_remove_local_from_ghost_state((uintptr_t) &cn_virt_ptr, sizeof(void*));

return __cn_ret;

}
