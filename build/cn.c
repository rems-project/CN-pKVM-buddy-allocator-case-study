#include "cn.h"
cn_bool* struct_exclude_none_record_equality(void* x, void* y)
{
  struct exclude_none_record* x_cast = (struct exclude_none_record*) x;
  struct exclude_none_record* y_cast = (struct exclude_none_record*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_bool_equality(x_cast->any, y_cast->any)), cn_bool_equality(x_cast->do_ex1, y_cast->do_ex1)), cn_bool_equality(x_cast->do_ex2, y_cast->do_ex2)), cn_bits_u64_equality(x_cast->ex1, y_cast->ex1)), cn_bits_u64_equality(x_cast->ex2, y_cast->ex2));
}

cn_bool* struct_exclude_one_record_equality(void* x, void* y)
{
  struct exclude_one_record* x_cast = (struct exclude_one_record*) x;
  struct exclude_one_record* y_cast = (struct exclude_one_record*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_bool_equality(x_cast->any, y_cast->any)), cn_bool_equality(x_cast->do_ex1, y_cast->do_ex1)), cn_bool_equality(x_cast->do_ex2, y_cast->do_ex2)), cn_bits_u64_equality(x_cast->ex1, y_cast->ex1)), cn_bits_u64_equality(x_cast->ex2, y_cast->ex2));
}

cn_bool* struct_exclude_two_record_equality(void* x, void* y)
{
  struct exclude_two_record* x_cast = (struct exclude_two_record*) x;
  struct exclude_two_record* y_cast = (struct exclude_two_record*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_bool_equality(x_cast->any, y_cast->any)), cn_bool_equality(x_cast->do_ex1, y_cast->do_ex1)), cn_bool_equality(x_cast->do_ex2, y_cast->do_ex2)), cn_bits_u64_equality(x_cast->ex1, y_cast->ex1)), cn_bits_u64_equality(x_cast->ex2, y_cast->ex2));
}

cn_bool* struct_Hyp_pool_ex1_record_equality(void* x, void* y)
{
  struct Hyp_pool_ex1_record* x_cast = (struct Hyp_pool_ex1_record*) x;
  struct Hyp_pool_ex1_record* y_cast = (struct Hyp_pool_ex1_record*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_map_equality(x_cast->APs, y_cast->APs, struct_list_head_cn_equality)), struct_hyp_pool_cn_equality(x_cast->pool, y_cast->pool)), cn_map_equality(x_cast->vmemmap, y_cast->vmemmap, struct_hyp_page_cn_equality));
}

cn_bool* struct_Hyp_pool_ex2_record_equality(void* x, void* y)
{
  struct Hyp_pool_ex2_record* x_cast = (struct Hyp_pool_ex2_record*) x;
  struct Hyp_pool_ex2_record* y_cast = (struct Hyp_pool_ex2_record*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_map_equality(x_cast->APs, y_cast->APs, struct_list_head_cn_equality)), struct_hyp_pool_cn_equality(x_cast->pool, y_cast->pool)), cn_map_equality(x_cast->vmemmap, y_cast->vmemmap, struct_hyp_page_cn_equality));
}

cn_bool* struct_Hyp_pool_record_equality(void* x, void* y)
{
  struct Hyp_pool_record* x_cast = (struct Hyp_pool_record*) x;
  struct Hyp_pool_record* y_cast = (struct Hyp_pool_record*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_map_equality(x_cast->APs, y_cast->APs, struct_list_head_cn_equality)), struct_hyp_pool_cn_equality(x_cast->pool, y_cast->pool)), cn_map_equality(x_cast->vmemmap, y_cast->vmemmap, struct_hyp_page_cn_equality));
}

struct exclude_none_record* default_struct_exclude_none_record()
{
  struct exclude_none_record* a_13836 = alloc(sizeof(struct exclude_none_record));
  a_13836->any = default_cn_bool();
  a_13836->do_ex1 = default_cn_bool();
  a_13836->do_ex2 = default_cn_bool();
  a_13836->ex1 = default_cn_bits_u64();
  a_13836->ex2 = default_cn_bits_u64();
  return a_13836;
}

struct exclude_one_record* default_struct_exclude_one_record()
{
  struct exclude_one_record* a_13849 = alloc(sizeof(struct exclude_one_record));
  a_13849->any = default_cn_bool();
  a_13849->do_ex1 = default_cn_bool();
  a_13849->do_ex2 = default_cn_bool();
  a_13849->ex1 = default_cn_bits_u64();
  a_13849->ex2 = default_cn_bits_u64();
  return a_13849;
}

struct exclude_two_record* default_struct_exclude_two_record()
{
  struct exclude_two_record* a_13862 = alloc(sizeof(struct exclude_two_record));
  a_13862->any = default_cn_bool();
  a_13862->do_ex1 = default_cn_bool();
  a_13862->do_ex2 = default_cn_bool();
  a_13862->ex1 = default_cn_bits_u64();
  a_13862->ex2 = default_cn_bits_u64();
  return a_13862;
}

struct Hyp_pool_ex1_record* default_struct_Hyp_pool_ex1_record()
{
  struct Hyp_pool_ex1_record* a_13875 = alloc(sizeof(struct Hyp_pool_ex1_record));
  a_13875->APs = default_cn_map();
  a_13875->pool = default_struct_hyp_pool_cn();
  a_13875->vmemmap = default_cn_map();
  return a_13875;
}

struct Hyp_pool_ex2_record* default_struct_Hyp_pool_ex2_record()
{
  struct Hyp_pool_ex2_record* a_13887 = alloc(sizeof(struct Hyp_pool_ex2_record));
  a_13887->APs = default_cn_map();
  a_13887->pool = default_struct_hyp_pool_cn();
  a_13887->vmemmap = default_cn_map();
  return a_13887;
}

struct Hyp_pool_record* default_struct_Hyp_pool_record()
{
  struct Hyp_pool_record* a_13899 = alloc(sizeof(struct Hyp_pool_record));
  a_13899->APs = default_cn_map();
  a_13899->pool = default_struct_hyp_pool_cn();
  a_13899->vmemmap = default_cn_map();
  return a_13899;
}

void* cn_map_get_struct_exclude_none_record(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_exclude_none_record();
  else
    return ret;
}

void* cn_map_get_struct_exclude_one_record(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_exclude_one_record();
  else
    return ret;
}

void* cn_map_get_struct_exclude_two_record(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_exclude_two_record();
  else
    return ret;
}

void* cn_map_get_struct_Hyp_pool_ex1_record(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_Hyp_pool_ex1_record();
  else
    return ret;
}

void* cn_map_get_struct_Hyp_pool_ex2_record(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_Hyp_pool_ex2_record();
  else
    return ret;
}

void* cn_map_get_struct_Hyp_pool_record(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_Hyp_pool_record();
  else
    return ret;
}

/* GENERATED STRUCT FUNCTIONS */

struct list_head_cn* convert_to_struct_list_head_cn(struct list_head list_head)
{
  struct list_head_cn* res = alloc(sizeof(struct list_head_cn));
  res->next = convert_to_cn_pointer(list_head.next);
  res->prev = convert_to_cn_pointer(list_head.prev);
  return res;
}

struct hyp_pool_cn* convert_to_struct_hyp_pool_cn(struct hyp_pool hyp_pool)
{
  struct hyp_pool_cn* res = alloc(sizeof(struct hyp_pool_cn));
  res->free_area = convert_to_cn_map(hyp_pool.free_area, convert_to_struct_list_head_cn, 11);
  res->range_start = convert_to_cn_bits_u64(hyp_pool.range_start);
  res->range_end = convert_to_cn_bits_u64(hyp_pool.range_end);
  res->max_order = convert_to_cn_bits_u8(hyp_pool.max_order);
  return res;
}

struct hyp_page_cn* convert_to_struct_hyp_page_cn(struct hyp_page hyp_page)
{
  struct hyp_page_cn* res = alloc(sizeof(struct hyp_page_cn));
  res->refcount = convert_to_cn_bits_u16(hyp_page.refcount);
  res->order = convert_to_cn_bits_u8(hyp_page.order);
  res->flags = convert_to_cn_bits_u8(hyp_page.flags);
  return res;
}

cn_bool* struct_list_head_cn_equality(void* x, void* y)
{
  struct list_head_cn* x_cast = (struct list_head_cn*) x;
  struct list_head_cn* y_cast = (struct list_head_cn*) y;
  return cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_pointer_equality(x_cast->next, y_cast->next)), cn_pointer_equality(x_cast->prev, y_cast->prev));
}

cn_bool* struct_hyp_pool_cn_equality(void* x, void* y)
{
  struct hyp_pool_cn* x_cast = (struct hyp_pool_cn*) x;
  struct hyp_pool_cn* y_cast = (struct hyp_pool_cn*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_map_equality(x_cast->free_area, y_cast->free_area, struct_list_head_cn_equality)), cn_bits_u64_equality(x_cast->range_start, y_cast->range_start)), cn_bits_u64_equality(x_cast->range_end, y_cast->range_end)), cn_bits_u8_equality(x_cast->max_order, y_cast->max_order));
}

cn_bool* struct_hyp_page_cn_equality(void* x, void* y)
{
  struct hyp_page_cn* x_cast = (struct hyp_page_cn*) x;
  struct hyp_page_cn* y_cast = (struct hyp_page_cn*) y;
  return cn_bool_and(cn_bool_and(cn_bool_and(convert_to_cn_bool(true), cn_bits_u16_equality(x_cast->refcount, y_cast->refcount)), cn_bits_u8_equality(x_cast->order, y_cast->order)), cn_bits_u8_equality(x_cast->flags, y_cast->flags));
}

void* cn_map_get_struct_list_head_cn(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_list_head_cn();
  else
    return ret;
}

void* cn_map_get_struct_hyp_pool_cn(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_hyp_pool_cn();
  else
    return ret;
}

void* cn_map_get_struct_hyp_page_cn(cn_map* m, cn_integer* key)
{
  void* ret = ht_get(m, (&key->val));
  if (0 == ret)
    return (void*) default_struct_hyp_page_cn();
  else
    return ret;
}

struct list_head_cn* default_struct_list_head_cn()
{
  struct list_head_cn* a_13606 = alloc(sizeof(struct list_head_cn));
  a_13606->next = default_cn_pointer();
  a_13606->prev = default_cn_pointer();
  return a_13606;
}

struct hyp_pool_cn* default_struct_hyp_pool_cn()
{
  struct hyp_pool_cn* a_13614 = alloc(sizeof(struct hyp_pool_cn));
  a_13614->free_area = default_cn_map();
  a_13614->range_start = default_cn_bits_u64();
  a_13614->range_end = default_cn_bits_u64();
  a_13614->max_order = default_cn_bits_u8();
  return a_13614;
}

struct hyp_page_cn* default_struct_hyp_page_cn()
{
  struct hyp_page_cn* a_13627 = alloc(sizeof(struct hyp_page_cn));
  a_13627->refcount = default_cn_bits_u16();
  a_13627->order = default_cn_bits_u8();
  a_13627->flags = default_cn_bits_u8();
  return a_13627;
}

/* OWNERSHIP FUNCTIONS */

struct list_head_cn* owned_struct_list_head(cn_pointer* cn_ptr, enum OWNERSHIP owned_enum)
{
  uintptr_t generic_c_ptr = (uintptr_t) (struct list_head*) cn_ptr->ptr;
  cn_check_ownership(owned_enum, generic_c_ptr, sizeof(struct list_head));
  return convert_to_struct_list_head_cn((*(struct list_head*) cn_ptr->ptr));
}

struct hyp_page_cn* owned_struct_hyp_page(cn_pointer* cn_ptr, enum OWNERSHIP owned_enum)
{
  uintptr_t generic_c_ptr = (uintptr_t) (struct hyp_page*) cn_ptr->ptr;
  cn_check_ownership(owned_enum, generic_c_ptr, sizeof(struct hyp_page));
  return convert_to_struct_hyp_page_cn((*(struct hyp_page*) cn_ptr->ptr));
}

struct hyp_pool_cn* owned_struct_hyp_pool(cn_pointer* cn_ptr, enum OWNERSHIP owned_enum)
{
  uintptr_t generic_c_ptr = (uintptr_t) (struct hyp_pool*) cn_ptr->ptr;
  cn_check_ownership(owned_enum, generic_c_ptr, sizeof(struct hyp_pool));
  return convert_to_struct_hyp_pool_cn((*(struct hyp_pool*) cn_ptr->ptr));
}

cn_bits_u8* owned_char(cn_pointer* cn_ptr, enum OWNERSHIP owned_enum)
{
  uintptr_t generic_c_ptr = (uintptr_t) (char*) cn_ptr->ptr;
  cn_check_ownership(owned_enum, generic_c_ptr, sizeof(char));
  return convert_to_cn_bits_u8((*(char*) cn_ptr->ptr));
}

cn_pointer* owned_void_pointer(cn_pointer* cn_ptr, enum OWNERSHIP owned_enum)
{
  uintptr_t generic_c_ptr = (uintptr_t) (void**) cn_ptr->ptr;
  cn_check_ownership(owned_enum, generic_c_ptr, sizeof(void*));
  return convert_to_cn_pointer((*(void**) cn_ptr->ptr));
}

cn_bits_i64* owned_signed_long_long(cn_pointer* cn_ptr, enum OWNERSHIP owned_enum)
{
  uintptr_t generic_c_ptr = (uintptr_t) (signed long long*) cn_ptr->ptr;
  cn_check_ownership(owned_enum, generic_c_ptr, sizeof(signed long long));
  return convert_to_cn_bits_i64((*(signed long long*) cn_ptr->ptr));
}

cn_pointer* owned_struct_hyp_page_pointer(cn_pointer* cn_ptr, enum OWNERSHIP owned_enum)
{
  uintptr_t generic_c_ptr = (uintptr_t) (struct hyp_page**) cn_ptr->ptr;
  cn_check_ownership(owned_enum, generic_c_ptr, sizeof(struct hyp_page*));
  return convert_to_cn_pointer((*(struct hyp_page**) cn_ptr->ptr));
}
cn_bits_u64* max_pfn()
{
  return cn_bits_u64_shift_right(cn_bits_u64_sub(convert_to_cn_bits_u64(0), convert_to_cn_bits_u64(1)), cast_cn_bits_i32_to_cn_bits_u64(convert_to_cn_bits_i32(12)));
}

cn_pointer* copy_alloc_id_cn(cn_bits_u64* x, cn_pointer* p)
{
  return cn_array_shift(p, sizeof(char), cn_bits_u64_sub(x, cast_cn_pointer_to_cn_bits_u64(p)));
}

cn_bits_u64* page_size()
{
  return convert_to_cn_bits_u64(4096);
}

cn_bits_u8* max_order()
{
  return convert_to_cn_bits_u8(11);
}

cn_bits_u8* hyp_no_order()
{
  return convert_to_cn_bits_u8(255);
}

cn_bits_u64* cn_hyp_page_to_pfn(cn_pointer* hypvmemmap, cn_pointer* p)
{
  return cn_bits_u64_divide(cn_bits_u64_sub(cast_cn_pointer_to_cn_bits_u64(p), cast_cn_pointer_to_cn_bits_u64(hypvmemmap)), cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page))));
}

cn_bits_u64* cn__hyp_pa(cn_bits_i64* physvirtoffset, cn_pointer* virt)
{
  return cast_cn_bits_i64_to_cn_bits_u64(cn_bits_i64_add(cast_cn_pointer_to_cn_bits_i64(virt), physvirtoffset));
}

cn_bits_u64* cn_hyp_phys_to_pfn(cn_bits_u64* phys)
{
  update_cn_error_message_info("function (u64) cn_hyp_phys_to_pfn(u64 phys) {\n         ~~~~~~~~~^~ ./driver.pp.c:414:10-21 (cursor: 414:19)");
  return cn_bits_u64_divide(phys, page_size());
}

cn_bits_u64* cn_hyp_virt_to_pfn(cn_bits_i64* physvirtoffset, cn_pointer* virt)
{
  update_cn_error_message_info("function (u64) cn_hyp_virt_to_pfn (i64 physvirtoffset, pointer virt) {\n                     ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:419:22-54 (cursor: 419:32)");
  update_cn_error_message_info("function (u64) cn_hyp_virt_to_pfn (i64 physvirtoffset, pointer virt) {\n  ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:419:3-55 (cursor: 419:21)");
  return cn_hyp_phys_to_pfn(cn__hyp_pa(physvirtoffset, virt));
}

cn_bits_u64* cn_hyp_pfn_to_phys(cn_bits_u64* pfn)
{
  update_cn_error_message_info("function (u64) cn_hyp_pfn_to_phys(u64 pfn) {\n      ~~~~~~~~~^~ ./driver.pp.c:424:7-18 (cursor: 424:16)");
  return cn_bits_u64_multiply(pfn, page_size());
}

cn_bits_u64* cn_hyp_page_to_phys(cn_pointer* hypvmemmap, cn_pointer* page)
{
  update_cn_error_message_info("function (u64) cn_hyp_page_to_phys(pointer hypvmemmap, pointer page) {\n                      ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:429:23-59 (cursor: 429:41)");
  update_cn_error_message_info("function (u64) cn_hyp_page_to_phys(pointer hypvmemmap, pointer page) {\n  ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:429:3-61 (cursor: 429:21)");
  return cn_hyp_pfn_to_phys(cn_hyp_page_to_pfn(hypvmemmap, page));
}

cn_pointer* cn__hyp_va(cn_pointer* virt_ptr, cn_bits_i64* physvirtoffset, cn_bits_u64* phys)
{
  update_cn_error_message_info("function (pointer) cn__hyp_va(pointer virt_ptr, i64 physvirtoffset, u64 phys) {\n  ~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:434:3-66 (cursor: 434:19)");
  return copy_alloc_id_cn(cast_cn_bits_i64_to_cn_bits_u64(cn_bits_i64_sub(cast_cn_bits_u64_to_cn_bits_i64(phys), physvirtoffset)), virt_ptr);
}

cn_pointer* cn_hyp_page_to_virt(cn_pointer* virt_ptr, cn_bits_i64* physvirtoffset, cn_pointer* hypvmemmap, cn_pointer* page)
{
  update_cn_error_message_info("                                       pointer hypvmemmap, pointer page) {\n                                       ~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~ ./driver.pp.c:440:40-77 (cursor: 440:59)");
  update_cn_error_message_info("                                       pointer hypvmemmap, pointer page) {\n  ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:440:3-78 (cursor: 440:13)");
  return cn__hyp_va(virt_ptr, physvirtoffset, cn_hyp_page_to_phys(hypvmemmap, page));
}

cn_bits_u64* calc_buddy(cn_bits_u64* addr, cn_bits_u8* order)
{
  update_cn_error_message_info("function (u64) calc_buddy(u64 addr, u8 order) {\n                               ~~~~~~~~~^~ ./driver.pp.c:444:32-43 (cursor: 444:41)");
  return cn_bits_u64_xor(addr, cn_bits_u64_shift_left(page_size(), cast_cn_bits_u8_to_cn_bits_u64(order)));
}

cn_bits_u64* pfn_buddy(cn_bits_u64* x, cn_bits_u8* order)
{
  update_cn_error_message_info("function (u64) pfn_buddy (u64 x, u8 order) {\n                                 ~~~~~~~~~~~~~~~~~~^~~ ./driver.pp.c:448:34-55 (cursor: 448:52)");
  update_cn_error_message_info("function (u64) pfn_buddy (u64 x, u8 order) {\n                      ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:448:23-63 (cursor: 448:33)");
  update_cn_error_message_info("function (u64) pfn_buddy (u64 x, u8 order) {\n  ~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:448:3-64 (cursor: 448:22)");
  return cn_hyp_phys_to_pfn(calc_buddy(cn_hyp_pfn_to_phys(x), order));
}

cn_bool* order_aligned(cn_bits_u64* x, cn_bits_u8* order)
{
  return cn_bits_u64_equality(cn_bits_u64_mod(x, cn_bits_u64_shift_left(convert_to_cn_bits_u64(1), cast_cn_bits_u8_to_cn_bits_u64(order))), convert_to_cn_bits_u64(0));
}

cn_bits_u64* order_align(cn_bits_u64* x, cn_bits_u8* order)
{
  return cn_bits_u64_sub(x, cn_bits_u64_mod(x, cn_bits_u64_shift_left(convert_to_cn_bits_u64(1), cast_cn_bits_u8_to_cn_bits_u64(order))));
}

cn_bool* cellPointer(cn_pointer* base, cn_bits_u64* size, cn_bits_u64* starti, cn_bits_u64* endi, cn_pointer* p)
{
  cn_bits_u64* offset = cn_bits_u64_sub(cast_cn_pointer_to_cn_bits_u64(base), cast_cn_pointer_to_cn_bits_u64(p));
  cn_pointer* start = cn_array_shift(base, sizeof(char), cn_bits_u64_multiply(size, starti));
  cn_pointer* end = cn_array_shift(base, sizeof(char), cn_bits_u64_multiply(size, endi));
  return cn_bool_and(cn_bool_and(cn_pointer_le(start, p), cn_pointer_lt(p, end)), cn_bits_u64_equality(cn_bits_u64_mod(offset, size), convert_to_cn_bits_u64(0)));
}

cn_bits_u64* page_size_of_order(cn_bits_u8* order)
{
  return cn_bits_u64_shift_left(convert_to_cn_bits_u64(1), cn_bits_u64_add(cast_cn_bits_u8_to_cn_bits_u64(order), convert_to_cn_bits_u64(12)));
}

cn_bool* page_aligned(cn_bits_u64* ptr, cn_bits_u8* order)
{
  update_cn_error_message_info("function (boolean) page_aligned (u64 ptr, u8 order) {\n           ~~~~~~~~~~~~~~~~~~^~~~~~~ ./driver.pp.c:475:12-37 (cursor: 475:30)");
  return cn_bits_u64_equality(cn_bits_u64_mod(ptr, page_size_of_order(order)), convert_to_cn_bits_u64(0));
}

cn_bool* excluded(struct exclude_two_record* ex, cn_bits_u64* i)
{
  return cn_bool_and(ex->any, cn_bool_or(cn_bool_and(ex->do_ex1, cn_bits_u64_equality(i, ex->ex1)), cn_bool_and(ex->do_ex2, cn_bits_u64_equality(i, ex->ex2))));
}

struct exclude_none_record* exclude_none()
{
  struct exclude_none_record* a_11784 = alloc(sizeof(struct exclude_none_record));
  a_11784->any = convert_to_cn_bool(false);
  a_11784->do_ex1 = convert_to_cn_bool(false);
  a_11784->do_ex2 = convert_to_cn_bool(false);
  a_11784->ex1 = convert_to_cn_bits_u64(0);
  a_11784->ex2 = convert_to_cn_bits_u64(0);
  return a_11784;
}

struct exclude_one_record* exclude_one(cn_bits_u64* ex1)
{
  struct exclude_one_record* a_11804 = alloc(sizeof(struct exclude_one_record));
  a_11804->any = convert_to_cn_bool(true);
  a_11804->do_ex1 = convert_to_cn_bool(true);
  a_11804->do_ex2 = convert_to_cn_bool(false);
  a_11804->ex1 = ex1;
  a_11804->ex2 = convert_to_cn_bits_u64(0);
  return a_11804;
}

struct exclude_two_record* exclude_two(cn_bits_u64* ex1, cn_bits_u64* ex2)
{
  struct exclude_two_record* a_11823 = alloc(sizeof(struct exclude_two_record));
  a_11823->any = convert_to_cn_bool(true);
  a_11823->do_ex1 = convert_to_cn_bool(true);
  a_11823->do_ex2 = convert_to_cn_bool(true);
  a_11823->ex1 = ex1;
  a_11823->ex2 = ex2;
  return a_11823;
}

cn_bool* vmemmap_good_pointer(cn_bits_i64* physvirt_offset, cn_pointer* p, cn_map* vmemmap, cn_bits_u64* range_start, cn_bits_u64* range_end, struct exclude_two_record* ex)
{
  update_cn_error_message_info("{\n           ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:516:12-42 (cursor: 516:22)");
  cn_bits_u64* pa = cn__hyp_pa(physvirt_offset, p);
  update_cn_error_message_info("  let pa = cn__hyp_pa(physvirt_offset, p);\n            ~~~~~~~~~~~~~~~~~~^~~~ ./driver.pp.c:517:13-35 (cursor: 517:31)");
  cn_bits_u64* pfn = cn_hyp_phys_to_pfn(pa);
  update_cn_error_message_info("  let pfn = cn_hyp_phys_to_pfn(pa);\n             ~~~~~~~~~~^~ ./driver.pp.c:518:14-26 (cursor: 518:24)");
  update_cn_error_message_info("    && (vmemmap[pfn].refcount == 0u16)\n                               ~~~~~~~~~~~~~^~ ./driver.pp.c:522:32-47 (cursor: 522:45)");
  update_cn_error_message_info("    && (vmemmap[pfn].order != (hyp_no_order ()))\n             ~~~~~~~~~^~~~~~~~~ ./driver.pp.c:523:14-32 (cursor: 523:23)");
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bits_u64_equality(cn_bits_u64_mod(pa, page_size()), convert_to_cn_bits_u64(0)), cn_bits_u64_le(range_start, pa)), cn_bits_u64_lt(pa, range_end)), cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(pfn)))->refcount, convert_to_cn_bits_u16(0))), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(pfn)))->order, hyp_no_order()))), cn_bool_not(excluded(ex, pfn)));
}

cn_bool* page_group_ok(cn_bits_u64* page_index, cn_map* vmemmap, struct hyp_pool_cn* pool)
{
  struct hyp_page_cn* page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(page_index));
  update_cn_error_message_info("  let page = vmemmap[page_index];\n                                      ~~~~~~~~~~^~ ./driver.pp.c:531:39-51 (cursor: 531:49)");
  cn_bits_u64* start_i = cn_bits_u64_divide(pool->range_start, page_size());
  update_cn_error_message_info("  let start_i = (pool.range_start) / (page_size ());\n                  ~~~~~~~~~~~~^~ ./driver.pp.c:532:19-33 (cursor: 532:31)");
  cn_bool* a_11946 = convert_to_cn_bool(true);
  {
    cn_bits_u8* i = convert_to_cn_bits_u8(1);
    while (convert_from_cn_bool(cn_bits_u8_lt(i, convert_to_cn_bits_u8(10)))) {
      update_cn_error_message_info("    || (each (u8 i: 1, 10; (not (\n         ~~~~~~~~~~~^~~~~~~~~~~~~~~ ./driver.pp.c:534:10-36 (cursor: 534:21)");
      update_cn_error_message_info("        (order_align(page_index, i) < page_index)\n                       ~~~~~~~~~~~^~~~~~~~~~~~~~~ ./driver.pp.c:535:24-50 (cursor: 535:35)");
      update_cn_error_message_info("        && (start_i <= order_align(page_index, i))\n                           ~~~~~~~~~~~^~~~~~~~~~~~~~~ ./driver.pp.c:536:28-54 (cursor: 536:39)");
      update_cn_error_message_info("        && (i <= (vmemmap[(order_align(page_index, i))]).order)\n                      ~~~~~~~~~~~^~~~~~~~~~~~~~~ ./driver.pp.c:537:23-49 (cursor: 537:34)");
      update_cn_error_message_info("        && (i <= (vmemmap[(order_align(page_index, i))]).order)\n                                                             ~~~~~~~~~~~~^~ ./driver.pp.c:537:62-76 (cursor: 537:74)");
      a_11946 = cn_bool_and(a_11946, cn_bool_not(cn_bool_and(cn_bool_and(cn_bool_and(cn_bits_u64_lt(order_align(page_index, i), page_index), cn_bits_u64_le(start_i, order_align(page_index, i))), cn_bits_u8_le(i, ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(order_align(page_index, i))))->order)), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(order_align(page_index, i))))->order, hyp_no_order())))));
      cn_bits_u8_increment(i);
    }
  }
  return cn_bool_or(cn_bits_u8_equality(page->order, hyp_no_order()), a_11946);
}

cn_bool* init_vmemmap_page(cn_bits_u64* page_index, cn_map* vmemmap, cn_pointer* pool_pointer, struct hyp_pool_cn* pool)
{
  struct hyp_page_cn* page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(page_index));
  update_cn_error_message_info("    && (page.refcount == 1u16)\n        ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~ ./driver.pp.c:550:9-39 (cursor: 550:22)");
  update_cn_error_message_info("    && (order_aligned(page_index, 0u8))\n                        ~~~~~~~~~~^~ ./driver.pp.c:551:25-37 (cursor: 551:35)");
  update_cn_error_message_info("    && (order_aligned(page_index, 0u8))\n                                         ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:551:42-72 (cursor: 551:60)");
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bits_u8_equality(page->order, convert_to_cn_bits_u8(0)), cn_bits_u16_equality(page->refcount, convert_to_cn_bits_u16(1))), order_aligned(page_index, convert_to_cn_bits_u8(0))), cn_bits_u64_le(cn_bits_u64_add(cn_bits_u64_multiply(page_index, page_size()), page_size_of_order(page->order)), pool->range_end));
}

cn_bool* vmemmap_normal_order_wf(cn_bits_u64* page_index, struct hyp_page_cn* page, struct hyp_pool_cn* pool)
{
  update_cn_error_message_info("function (boolean) vmemmap_normal_order_wf (u64 page_index, struct hyp_page page, struct hyp_pool pool) {\n                                                                          ~~~~~~~~~^~ ./driver.pp.c:555:75-86 (cursor: 555:84)");
  update_cn_error_message_info("    (0u8 <= page.order && ((page.order < pool.max_order) && (page.order < max_order())))\n       ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:556:8-45 (cursor: 556:21)");
  update_cn_error_message_info("    && order_aligned(page_index, page.order)\n                        ~~~~~~~~~~^~ ./driver.pp.c:557:25-37 (cursor: 557:35)");
  update_cn_error_message_info("    && order_aligned(page_index, page.order)\n                                         ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:557:42-72 (cursor: 557:60)");
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bits_u8_le(convert_to_cn_bits_u8(0), page->order), cn_bool_and(cn_bits_u8_lt(page->order, pool->max_order), cn_bits_u8_lt(page->order, max_order()))), order_aligned(page_index, page->order)), cn_bits_u64_le(cn_bits_u64_add(cn_bits_u64_multiply(page_index, page_size()), page_size_of_order(page->order)), pool->range_end));
}

cn_bool* vmemmap_wf(cn_bits_u64* page_index, cn_map* vmemmap, cn_pointer* pool_pointer, struct hyp_pool_cn* pool)
{
  struct hyp_page_cn* page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(page_index));
  update_cn_error_message_info("  let page = vmemmap[page_index];\n                     ~~~~~~~~~~~~~^~ ./driver.pp.c:565:22-37 (cursor: 565:35)");
  update_cn_error_message_info("  let page = vmemmap[page_index];\n                                          ~~~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:565:43-90 (cursor: 565:66)");
  update_cn_error_message_info("    ((page.order == (hyp_no_order ())) || vmemmap_normal_order_wf(page_index, page, pool))\n                       ~~~~~~~~~~~~^~ ./driver.pp.c:566:24-38 (cursor: 566:36)");
  update_cn_error_message_info("    && ((page.order != hyp_no_order()) || (page.refcount == 0u16))\n        ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:567:9-49 (cursor: 567:22)");
  return cn_bool_and(cn_bool_and(cn_bool_or(cn_bits_u8_equality(page->order, hyp_no_order()), vmemmap_normal_order_wf(page_index, page, pool)), cn_bool_or(cn_bool_not(cn_bits_u8_equality(page->order, hyp_no_order())), cn_bits_u16_equality(page->refcount, convert_to_cn_bits_u16(0)))), page_group_ok(page_index, vmemmap, pool));
}

cn_bool* vmemmap_l_wf(cn_bits_u64* page_index, cn_bits_i64* physvirt_offset, cn_pointer* virt_ptr, cn_map* vmemmap, cn_map* APs, cn_pointer* pool_pointer, struct hyp_pool_cn* pool, struct exclude_two_record* ex)
{
  struct hyp_page_cn* page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(page_index));
  update_cn_error_message_info("  let page = vmemmap[page_index];\n                                                                ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~ ./driver.pp.c:576:65-95 (cursor: 576:83)");
  update_cn_error_message_info("  let page = vmemmap[page_index];\n                          ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:576:27-96 (cursor: 576:37)");
  cn_pointer* self_node_pointer = cn__hyp_va(virt_ptr, physvirt_offset, cn_hyp_pfn_to_phys(page_index));
  cn_pointer* pool_free_area_arr_pointer = cn_member_shift(pool_pointer, hyp_pool, free_area);
  cn_pointer* pool_free_area_pointer = cn_array_shift(pool_free_area_arr_pointer, sizeof(struct list_head), page->order);
  cn_pointer* prev = ((struct list_head_cn*) cn_map_get_struct_list_head_cn(APs, cast_cn_bits_u64_to_cn_integer(page_index)))->prev;
  cn_pointer* next = ((struct list_head_cn*) cn_map_get_struct_list_head_cn(APs, cast_cn_bits_u64_to_cn_integer(page_index)))->next;
  struct list_head_cn* free_area_entry = (struct list_head_cn*) cn_map_get_struct_list_head_cn(pool->free_area, cast_cn_bits_u64_to_cn_integer(cast_cn_bits_u8_to_cn_bits_u64(page->order)));
  cn_pointer* prev_page_pointer = prev;
  update_cn_error_message_info("  let prev_page_pointer = prev;\n                        ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:583:25-79 (cursor: 583:43)");
  cn_bits_u64* prev_page_index = cn_hyp_virt_to_pfn(physvirt_offset, prev_page_pointer);
  struct hyp_page_cn* prev_page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(prev_page_index));
  cn_pointer* next_page_pointer = next;
  update_cn_error_message_info("  let next_page_pointer = next;\n                        ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:586:25-79 (cursor: 586:43)");
  cn_bits_u64* next_page_index = cn_hyp_virt_to_pfn(physvirt_offset, next_page_pointer);
  struct hyp_page_cn* next_page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(next_page_index));
  cn_alloc_id* prov = convert_to_cn_alloc_id(0);
  update_cn_error_message_info("    ((prev == pool_free_area_pointer) && (free_area_entry.next == self_node_pointer))\n        ~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:591:9-113 (cursor: 591:30)");
  cn_bool* prev_clause = cn_bool_or(cn_bool_and(cn_pointer_equality(prev, pool_free_area_pointer), cn_pointer_equality(free_area_entry->next, self_node_pointer)), cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(vmemmap_good_pointer(physvirt_offset, prev_page_pointer, vmemmap, pool->range_start, pool->range_end, ex), cn_alloc_id_equality(prov, convert_to_cn_alloc_id(0))), cn_pointer_equality(((struct list_head_cn*) cn_map_get_struct_list_head_cn(APs, cast_cn_bits_u64_to_cn_integer(prev_page_index)))->next, self_node_pointer)), cn_bits_u8_equality(prev_page->order, page->order)), cn_bits_u16_equality(prev_page->refcount, convert_to_cn_bits_u16(0))));
  update_cn_error_message_info("    ((next == pool_free_area_pointer) && (free_area_entry.prev == self_node_pointer))\n        ~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:598:9-113 (cursor: 598:30)");
  cn_bool* next_clause = cn_bool_or(cn_bool_and(cn_pointer_equality(next, pool_free_area_pointer), cn_pointer_equality(free_area_entry->prev, self_node_pointer)), cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(vmemmap_good_pointer(physvirt_offset, next_page_pointer, vmemmap, pool->range_start, pool->range_end, ex), cn_alloc_id_equality(prov, convert_to_cn_alloc_id(0))), cn_pointer_equality(((struct list_head_cn*) cn_map_get_struct_list_head_cn(APs, cast_cn_bits_u64_to_cn_integer(next_page_index)))->prev, self_node_pointer)), cn_bits_u8_equality(next_page->order, page->order)), cn_bits_u16_equality(next_page->refcount, convert_to_cn_bits_u16(0))));
  cn_bool* nonempty_clause = cn_bool_and(cn_bool_not(cn_pointer_equality(prev, self_node_pointer)), cn_bool_not(cn_pointer_equality(next, self_node_pointer)));
  return cn_bool_and(prev_clause, next_clause);
}

cn_bool* freeArea_cell_wf(cn_bits_u8* cell_index, cn_bits_i64* physvirt_offset, cn_pointer* virt_ptr, cn_map* vmemmap, cn_map* APs, cn_pointer* pool_pointer, struct hyp_pool_cn* pool, struct exclude_two_record* ex)
{
  struct list_head_cn* cell = (struct list_head_cn*) cn_map_get_struct_list_head_cn(pool->free_area, cast_cn_bits_u64_to_cn_integer(cast_cn_bits_u8_to_cn_bits_u64(cell_index)));
  cn_pointer* pool_free_area_arr_pointer = cn_member_shift(pool_pointer, hyp_pool, free_area);
  cn_pointer* cell_pointer = cn_array_shift(pool_free_area_arr_pointer, sizeof(struct list_head), cell_index);
  cn_pointer* prev = cell->prev;
  cn_pointer* next = cell->next;
  cn_pointer* prev_page_pointer = prev;
  update_cn_error_message_info("  let prev_page_pointer = prev;\n                        ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:622:25-79 (cursor: 622:43)");
  cn_bits_u64* prev_page_index = cn_hyp_virt_to_pfn(physvirt_offset, prev_page_pointer);
  struct hyp_page_cn* prev_page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(prev_page_index));
  cn_pointer* next_page_pointer = next;
  update_cn_error_message_info("  let next_page_pointer = next;\n                        ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:625:25-79 (cursor: 625:43)");
  cn_bits_u64* next_page_index = cn_hyp_virt_to_pfn(physvirt_offset, next_page_pointer);
  struct hyp_page_cn* next_page = (struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(vmemmap, cast_cn_bits_u64_to_cn_integer(next_page_index));
  update_cn_error_message_info("        ((alloc_id) prev == (alloc_id) virt_ptr)\n            ~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:630:13-117 (cursor: 630:34)");
  update_cn_error_message_info("        && (ptr_eq(next, cell_pointer) || !addr_eq(next, cell_pointer))\n            ~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:636:13-117 (cursor: 636:34)");
  return cn_bool_and(cn_bool_equality(cn_pointer_equality(prev, cell_pointer), cn_pointer_equality(next, cell_pointer)), cn_bool_or(cn_pointer_equality(prev, cell_pointer), cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0)), vmemmap_good_pointer(physvirt_offset, prev_page_pointer, vmemmap, pool->range_start, pool->range_end, ex)), cn_bits_u8_equality(prev_page->order, cell_index)), cn_bits_u16_equality(prev_page->refcount, convert_to_cn_bits_u16(0))), cn_pointer_equality(((struct list_head_cn*) cn_map_get_struct_list_head_cn(APs, cast_cn_bits_u64_to_cn_integer(prev_page_index)))->next, cell_pointer)), cn_alloc_id_equality(convert_to_cn_alloc_id(0), convert_to_cn_alloc_id(0))), cn_bool_or(cn_pointer_equality(next, cell_pointer), cn_bool_not(cn_bits_u64_equality(cast_cn_pointer_to_cn_bits_u64(next), cast_cn_pointer_to_cn_bits_u64(cell_pointer))))), vmemmap_good_pointer(physvirt_offset, next_page_pointer, vmemmap, pool->range_start, pool->range_end, ex)), cn_bits_u8_equality(next_page->order, cell_index)), cn_bits_u16_equality(next_page->refcount, convert_to_cn_bits_u16(0))), cn_pointer_equality(((struct list_head_cn*) cn_map_get_struct_list_head_cn(APs, cast_cn_bits_u64_to_cn_integer(next_page_index)))->prev, cell_pointer))));
}

cn_bool* hyp_pool_wf(cn_pointer* pool_pointer, struct hyp_pool_cn* pool, cn_pointer* vmemmap_pointer, cn_bits_i64* physvirt_offset)
{
  cn_bits_u64* range_start = pool->range_start;
  cn_bits_u64* range_end = pool->range_end;
  update_cn_error_message_info("  let range_end = pool.range_end;\n                              ~~~~~~~~~~^~ ./driver.pp.c:648:31-43 (cursor: 648:41)");
  cn_bits_u64* start_i = cn_bits_u64_divide(range_start, page_size());
  update_cn_error_message_info("  let start_i = range_start / page_size ();\n                          ~~~~~~~~~~^~ ./driver.pp.c:649:27-39 (cursor: 649:37)");
  cn_bits_u64* end_i = cn_bits_u64_divide(range_end, page_size());
  cn_bits_u64* hp_sz = convert_to_cn_bits_u64(sizeof(struct hyp_page));
  cn_bits_u64* pool_sz = convert_to_cn_bits_u64(sizeof(struct hyp_pool));
  cn_pointer* vmemmap_start_pointer = cn_array_shift(vmemmap_pointer, sizeof(struct hyp_page), start_i);
  cn_pointer* vmemmap_boundary_pointer = cn_array_shift(vmemmap_pointer, sizeof(struct hyp_page), end_i);
  cn_bits_u64* range_start_virt = cast_cn_bits_i64_to_cn_bits_u64(cn_bits_i64_sub(cast_cn_bits_u64_to_cn_bits_i64(range_start), physvirt_offset));
  cn_bits_u64* range_end_virt = cast_cn_bits_i64_to_cn_bits_u64(cn_bits_i64_sub(cast_cn_bits_u64_to_cn_bits_i64(range_end), physvirt_offset));
  update_cn_error_message_info("    && (physvirt_offset < (i64) range_start) // use '<='\n                                    ~~~~~~~~~~^~ ./driver.pp.c:659:37-49 (cursor: 659:47)");
  update_cn_error_message_info("    && (mod((u64) physvirt_offset, (page_size ())) == 0u64)\n                         ~~~~~~~~~~^~ ./driver.pp.c:660:26-38 (cursor: 660:36)");
  update_cn_error_message_info("    && (mod((u64) physvirt_offset, (page_size ())) == 0u64)\n                                           ~~~~~~~~~~^~ ./driver.pp.c:660:44-56 (cursor: 660:54)");
  update_cn_error_message_info("    && (((range_start / (page_size ())) * (page_size ())) == range_start)\n                       ~~~~~~~~~~^~ ./driver.pp.c:661:24-36 (cursor: 661:34)");
  update_cn_error_message_info("    && (((range_start / (page_size ())) * (page_size ())) == range_start)\n                                         ~~~~~~~~~~^~ ./driver.pp.c:661:42-54 (cursor: 661:52)");
  update_cn_error_message_info("    && (((range_end / (page_size ())) * (page_size ())) == range_end)\n                           ~~~~~~~~~~^~ ./driver.pp.c:662:28-40 (cursor: 662:38)");
  return cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bool_and(cn_bits_u64_lt(range_start, range_end), cn_bits_u64_lt(range_end, cn_bits_u64_shift_left(convert_to_cn_bits_u64(1), convert_to_cn_bits_u64(52)))), cn_bits_i64_lt(physvirt_offset, cast_cn_bits_u64_to_cn_bits_i64(range_start))), cn_bits_u64_equality(cn_bits_u64_mod(cast_cn_bits_i64_to_cn_bits_u64(physvirt_offset), page_size()), convert_to_cn_bits_u64(0))), cn_bits_u64_equality(cn_bits_u64_multiply(cn_bits_u64_divide(range_start, page_size()), page_size()), range_start)), cn_bits_u64_equality(cn_bits_u64_multiply(cn_bits_u64_divide(range_end, page_size()), page_size()), range_end)), cn_bits_u8_le(pool->max_order, max_order())), cn_bits_u64_equality(cn_bits_u64_mod(cast_cn_pointer_to_cn_bits_u64(vmemmap_pointer), hp_sz), convert_to_cn_bits_u64(0))), cn_bool_or(cn_bits_u64_le(cn_bits_u64_add(cast_cn_pointer_to_cn_bits_u64(pool_pointer), pool_sz), cast_cn_pointer_to_cn_bits_u64(vmemmap_start_pointer)), cn_bits_u64_le(cast_cn_pointer_to_cn_bits_u64(vmemmap_boundary_pointer), cast_cn_pointer_to_cn_bits_u64(pool_pointer)))), cn_bool_or(cn_bits_u64_le(cn_bits_u64_add(cast_cn_pointer_to_cn_bits_u64(pool_pointer), pool_sz), range_start_virt), cn_bits_u64_le(range_end_virt, cast_cn_pointer_to_cn_bits_u64(pool_pointer))));
}

cn_bits_u8* get_order_uf(cn_bits_u64* size)
{
  return cast_cn_bits_u64_to_cn_bits_u8(cn_bits_u64_flsl(cn_bits_u64_shift_right(cn_bits_u64_sub(size, convert_to_cn_bits_u64(1)), convert_to_cn_bits_u64(12))));
}

cn_pointer* virt(cn_pointer* phys, cn_bits_i64* physvirt_offset)
{
  return cn_array_shift(phys, sizeof(char), cn_bits_i64_sub(convert_to_cn_bits_i64(0), physvirt_offset));
}

struct list_head_cn* todo_default_list_head()
{
  struct list_head_cn* a_12496 = alloc(sizeof(struct list_head_cn));
  a_12496->next = convert_to_cn_pointer(NULL);
  a_12496->prev = convert_to_cn_pointer(NULL);
  return a_12496;
}


/* CN PREDICATES */

void Byte(cn_pointer* virt, enum OWNERSHIP owned_enum)
{
  update_cn_error_message_info("unknown location");
  cn_bits_u8* B = owned_char(virt, owned_enum);
  return;
}

void ByteV(cn_pointer* virt, cn_bits_u8* the_value, enum OWNERSHIP owned_enum)
{
  update_cn_error_message_info("unknown location");
  cn_bits_u8* B = owned_char(virt, owned_enum);
  update_cn_error_message_info(NULL);
  cn_assert(cn_bits_u8_equality(B, the_value));
  return;
}

void Page(cn_pointer* vbase, cn_bool* guard, cn_bits_u8* order, enum OWNERSHIP owned_enum)
{
  if (convert_from_cn_bool(cn_bool_not(guard))) {
    return;
  }
  else {
    update_cn_error_message_info("  else {\n                 ~~~~~~~~~~~~~~~~~~^~~~~~~ ./driver.pp.c:698:18-43 (cursor: 698:36)");
    cn_bits_u64* length = page_size_of_order(order);
    cn_bits_u64* vbaseI = cast_cn_pointer_to_cn_bits_u64(vbase);
    update_cn_error_message_info("    let vbaseI = (u64) vbase;\n         ^./driver.pp.c:700:10:");
    {
      cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(vbaseI);
      while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(vbaseI, i), cn_bits_u64_lt(i, cn_bits_u64_add(vbaseI, length))))) {
        if (convert_from_cn_bool(convert_to_cn_bool(true))) {
          cn_pointer* a_12560 = cn_pointer_add_cn_bits_u64(convert_to_cn_pointer(NULL), cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(char)))));
          Byte(a_12560, owned_enum);
        }
        else {
          ;
        }
        cn_bits_u64_increment(i);
      }
    }
    return;
  }
}

void ZeroPage(cn_pointer* vbase, cn_bool* guard, cn_bits_u8* order, enum OWNERSHIP owned_enum)
{
  if (convert_from_cn_bool(cn_bool_not(guard))) {
    return;
  }
  else {
    update_cn_error_message_info("  else {\n                 ~~~~~~~~~~~~~~~~~~^~~~~~~ ./driver.pp.c:712:18-43 (cursor: 712:36)");
    cn_bits_u64* length = page_size_of_order(order);
    cn_bits_u64* vbaseI = cast_cn_pointer_to_cn_bits_u64(vbase);
    update_cn_error_message_info("    let vbaseI = ((u64) vbase);\n         ^./driver.pp.c:714:10:");
    {
      cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(vbaseI);
      while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(vbaseI, i), cn_bits_u64_lt(i, cn_bits_u64_add(vbaseI, length))))) {
        if (convert_from_cn_bool(convert_to_cn_bool(true))) {
          cn_pointer* a_12610 = cn_pointer_add_cn_bits_u64(convert_to_cn_pointer(NULL), cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(char)))));
          ByteV(a_12610, convert_to_cn_bits_u8(0), owned_enum);
        }
        else {
          ;
        }
        cn_bits_u64_increment(i);
      }
    }
    return;
  }
}

void AllocatorPageZeroPart(cn_pointer* zero_start, cn_bits_u8* order, enum OWNERSHIP owned_enum)
{
  cn_bits_u64* start = cast_cn_pointer_to_cn_bits_u64(zero_start);
  update_cn_error_message_info("  let start = (u64) zero_start;\n                      ~~~~~~~~~~~~~~~~~~^~~~~~~ ./driver.pp.c:723:23-48 (cursor: 723:41)");
  cn_bits_u64* region_length = page_size_of_order(order);
  cn_bits_u64* length = cn_bits_u64_sub(region_length, convert_to_cn_bits_u64(sizeof(struct list_head)));
  update_cn_error_message_info("  let length = region_length - sizeof<struct list_head>;\n       ^./driver.pp.c:725:8:");
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start, i), cn_bits_u64_lt(i, cn_bits_u64_add(start, length))))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        cn_pointer* a_12664 = cn_pointer_add_cn_bits_u64(convert_to_cn_pointer(NULL), cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(char)))));
        ByteV(a_12664, convert_to_cn_bits_u8(0), owned_enum);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  return;
}

struct list_head_cn* AllocatorPage(cn_pointer* vbase, cn_bool* guard, cn_bits_u8* order, enum OWNERSHIP owned_enum)
{
  if (convert_from_cn_bool(cn_bool_not(guard))) {
    update_cn_error_message_info("  if (!guard) {\n            ~~~~~~~~~~~~~~~~~~~~~~~^~ ./driver.pp.c:738:13-38 (cursor: 738:36)");
    return todo_default_list_head();
  }
  else {
    cn_pointer* zero_start = cn_array_shift(vbase, sizeof(struct list_head), convert_to_cn_bits_u8(1));
    update_cn_error_message_info("    let zero_start = array_shift<struct list_head>(vbase, 1u8);\n         ^./driver.pp.c:742:10:");
    AllocatorPageZeroPart(zero_start, order, owned_enum);
    update_cn_error_message_info("unknown location");
    struct list_head_cn* Node = owned_struct_list_head(vbase, owned_enum);
    return Node;
  }
}

struct Hyp_pool_ex1_record* Hyp_pool_ex1(cn_pointer* pool_l, cn_pointer* vmemmap_l, cn_pointer* virt_ptr, cn_bits_i64* physvirt_offset, cn_bits_u64* ex1, enum OWNERSHIP owned_enum)
{
  update_cn_error_message_info("{\n           ~~~~~~~~~~~~^~~~~ ./driver.pp.c:762:12-29 (cursor: 762:24)");
  struct exclude_two_record* ex = exclude_one(ex1);
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* pool = owned_struct_hyp_pool(pool_l, owned_enum);
  update_cn_error_message_info("  take pool = Owned<struct hyp_pool>(pool_l);\n                                   ~~~~~~~~~^~ ./driver.pp.c:764:36-47 (cursor: 764:45)");
  cn_bits_u64* start_i = cn_bits_u64_divide(pool->range_start, page_size());
  update_cn_error_message_info("  let start_i = pool.range_start / page_size();\n                               ~~~~~~~~~^~ ./driver.pp.c:765:32-43 (cursor: 765:41)");
  cn_bits_u64* end_i = cn_bits_u64_divide(pool->range_end, page_size());
  update_cn_error_message_info("  let end_i = pool.range_end / page_size();\n          ~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:766:11-65 (cursor: 766:23)");
  update_cn_error_message_info(NULL);
  cn_assert(hyp_pool_wf(pool_l, pool, vmemmap_l, physvirt_offset));
  update_cn_error_message_info("unknown location");
  cn_map* V = map_create();
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        cn_pointer* a_12734 = cn_pointer_add_cn_bits_u64(vmemmap_l, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
        cn_map_set(V, cast_cn_bits_u64_to_cn_integer(i), owned_struct_hyp_page(a_12734, owned_enum));
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info("               {Owned(array_shift<struct hyp_page>(vmemmap_l, i))};\n                   ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:769:20-63 (cursor: 769:30)");
  cn_pointer* ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, convert_to_cn_bits_u64(0));
  update_cn_error_message_info("                  && ((V[i]).refcount == 0u16)\n                                       ~~~~~~~~~~~~~^~ ./driver.pp.c:772:40-55 (cursor: 772:53)");
  update_cn_error_message_info("                  && ((V[i]).order != (hyp_no_order ()))\n                            ~~~~~~~~~^~~~~~~ ./driver.pp.c:773:29-45 (cursor: 773:38)");
  update_cn_error_message_info("  let ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, 0u64);\n       ^./driver.pp.c:770:8:");
  cn_map* APs = map_create();
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(cn_bool_and(cn_bool_and(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, hyp_no_order()))), cn_bool_not(excluded(ex, i))))) {
        cn_pointer* a_12834 = cn_pointer_add_cn_bits_u64(ptr_phys_0, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(char[4096])))));
        cn_map_set(APs, cast_cn_bits_u64_to_cn_integer(i), AllocatorPage(a_12834, convert_to_cn_bool(true), ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, owned_enum));
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  cn_bool* a_12863 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        update_cn_error_message_info("  assert (each (u64 i; (start_i <= i) && (i < end_i))\n     ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:776:6-37 (cursor: 776:17)");
        a_12863 = cn_bool_and(a_12863, vmemmap_wf(i, V, pool_l, pool));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_12863);
  cn_bool* a_12909 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(cn_bool_and(cn_bool_and(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, hyp_no_order()))), cn_bool_not(excluded(ex, i))))) {
        update_cn_error_message_info("            && ((not (excluded (ex, i)))))\n     ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:781:6-75 (cursor: 781:19)");
        a_12909 = cn_bool_and(a_12909, vmemmap_l_wf(i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_12909);
  cn_bool* a_12931 = convert_to_cn_bool(true);
  {
    cn_bits_u8* i = cast_cn_bits_u8_to_cn_bits_u8(convert_to_cn_bits_u8(0));
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u8_le(convert_to_cn_bits_u8(0), i), cn_bits_u8_lt(i, pool->max_order)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        update_cn_error_message_info("  assert (each(u8 i; 0u8 <= i && i < pool.max_order)\n               ~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:783:16-89 (cursor: 783:33)");
        a_12931 = cn_bool_and(a_12931, freeArea_cell_wf(i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex));
        cn_bits_u8_increment(i);
      }
      else {
        ;
      }
      cn_bits_u8_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_12931);
  struct Hyp_pool_ex1_record* a_12940 = alloc(sizeof(struct Hyp_pool_ex1_record));
  a_12940->APs = APs;
  a_12940->pool = pool;
  a_12940->vmemmap = V;
  return a_12940;
}

struct Hyp_pool_ex2_record* Hyp_pool_ex2(cn_pointer* pool_l, cn_pointer* vmemmap_l, cn_pointer* virt_ptr, cn_bits_i64* physvirt_offset, cn_bits_u64* ex1, cn_bits_u64* ex2, enum OWNERSHIP owned_enum)
{
  update_cn_error_message_info("{\n           ~~~~~~~~~~~~^~~~~~~~~~ ./driver.pp.c:801:12-34 (cursor: 801:24)");
  struct exclude_two_record* ex = exclude_two(ex1, ex2);
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* pool = owned_struct_hyp_pool(pool_l, owned_enum);
  update_cn_error_message_info("  take pool = Owned<struct hyp_pool>(pool_l);\n                                   ~~~~~~~~~^~ ./driver.pp.c:803:36-47 (cursor: 803:45)");
  cn_bits_u64* start_i = cn_bits_u64_divide(pool->range_start, page_size());
  update_cn_error_message_info("  let start_i = pool.range_start / page_size();\n                               ~~~~~~~~~^~ ./driver.pp.c:804:32-43 (cursor: 804:41)");
  cn_bits_u64* end_i = cn_bits_u64_divide(pool->range_end, page_size());
  update_cn_error_message_info("  let end_i = pool.range_end / page_size();\n          ~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:805:11-65 (cursor: 805:23)");
  update_cn_error_message_info(NULL);
  cn_assert(hyp_pool_wf(pool_l, pool, vmemmap_l, physvirt_offset));
  update_cn_error_message_info("unknown location");
  cn_map* V = map_create();
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        cn_pointer* a_12994 = cn_pointer_add_cn_bits_u64(vmemmap_l, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
        cn_map_set(V, cast_cn_bits_u64_to_cn_integer(i), owned_struct_hyp_page(a_12994, owned_enum));
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info("              {Owned(array_shift<struct hyp_page>(vmemmap_l,  i))};\n                   ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:808:20-63 (cursor: 808:30)");
  cn_pointer* ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, convert_to_cn_bits_u64(0));
  update_cn_error_message_info("                  && ((V[i]).refcount == 0u16)\n                                       ~~~~~~~~~~~~~^~ ./driver.pp.c:811:40-55 (cursor: 811:53)");
  update_cn_error_message_info("                  && ((V[i]).order != (hyp_no_order ()))\n                            ~~~~~~~~~^~~~~~~ ./driver.pp.c:812:29-45 (cursor: 812:38)");
  update_cn_error_message_info("  let ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, 0u64);\n       ^./driver.pp.c:809:8:");
  cn_map* APs = map_create();
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(cn_bool_and(cn_bool_and(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, hyp_no_order()))), cn_bool_not(excluded(ex, i))))) {
        cn_pointer* a_13094 = cn_pointer_add_cn_bits_u64(ptr_phys_0, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(char[4096])))));
        cn_map_set(APs, cast_cn_bits_u64_to_cn_integer(i), AllocatorPage(a_13094, convert_to_cn_bool(true), ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, owned_enum));
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  cn_bool* a_13123 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        update_cn_error_message_info("  assert (each (u64 i; (start_i <= i) && (i < end_i))\n     ~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:815:6-37 (cursor: 815:17)");
        a_13123 = cn_bool_and(a_13123, vmemmap_wf(i, V, pool_l, pool));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_13123);
  cn_bool* a_13169 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(cn_bool_and(cn_bool_and(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, hyp_no_order()))), cn_bool_not(excluded(ex, i))))) {
        update_cn_error_message_info("            && ((not (excluded (ex, i)))))\n     ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:820:6-75 (cursor: 820:19)");
        a_13169 = cn_bool_and(a_13169, vmemmap_l_wf(i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_13169);
  cn_bool* a_13191 = convert_to_cn_bool(true);
  {
    cn_bits_u8* i = cast_cn_bits_u8_to_cn_bits_u8(convert_to_cn_bits_u8(0));
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u8_le(convert_to_cn_bits_u8(0), i), cn_bits_u8_lt(i, pool->max_order)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        update_cn_error_message_info("  assert (each(u8 i; 0u8 <= i && i < pool.max_order)\n               ~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:822:16-89 (cursor: 822:33)");
        a_13191 = cn_bool_and(a_13191, freeArea_cell_wf(i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex));
        cn_bits_u8_increment(i);
      }
      else {
        ;
      }
      cn_bits_u8_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_13191);
  struct Hyp_pool_ex2_record* a_13200 = alloc(sizeof(struct Hyp_pool_ex2_record));
  a_13200->APs = APs;
  a_13200->pool = pool;
  a_13200->vmemmap = V;
  return a_13200;
}

struct Hyp_pool_record* Hyp_pool(cn_pointer* pool_l, cn_pointer* vmemmap_l, cn_pointer* virt_ptr, cn_bits_i64* physvirt_offset, enum OWNERSHIP owned_enum)
{
  update_cn_error_message_info("{\n           ~~~~~~~~~~~~~^~ ./driver.pp.c:838:12-27 (cursor: 838:25)");
  struct exclude_two_record* ex = exclude_none();
  update_cn_error_message_info("unknown location");
  struct hyp_pool_cn* P = owned_struct_hyp_pool(pool_l, owned_enum);
  update_cn_error_message_info("  take P = Owned<struct hyp_pool>(pool_l);\n                                ~~~~~~~~~^~ ./driver.pp.c:840:33-44 (cursor: 840:42)");
  cn_bits_u64* start_i = cn_bits_u64_divide(P->range_start, page_size());
  update_cn_error_message_info("  let start_i = P.range_start / page_size();\n                            ~~~~~~~~~^~ ./driver.pp.c:841:29-40 (cursor: 841:38)");
  cn_bits_u64* end_i = cn_bits_u64_divide(P->range_end, page_size());
  update_cn_error_message_info("unknown location");
  cn_map* V = map_create();
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        cn_pointer* a_13253 = cn_pointer_add_cn_bits_u64(vmemmap_l, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(struct hyp_page)))));
        cn_map_set(V, cast_cn_bits_u64_to_cn_integer(i), owned_struct_hyp_page(a_13253, owned_enum));
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info("              {Owned(array_shift<struct hyp_page>(vmemmap_l, i))};\n          ~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:844:11-62 (cursor: 844:23)");
  update_cn_error_message_info(NULL);
  cn_assert(hyp_pool_wf(pool_l, P, vmemmap_l, physvirt_offset));
  update_cn_error_message_info("  assert (hyp_pool_wf (pool_l, P, vmemmap_l, physvirt_offset));\n                   ~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:845:20-63 (cursor: 845:30)");
  cn_pointer* ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, convert_to_cn_bits_u64(0));
  update_cn_error_message_info("                  && ((V[i]).refcount == 0u16)\n                                       ~~~~~~~~~~~~~^~ ./driver.pp.c:848:40-55 (cursor: 848:53)");
  update_cn_error_message_info("                  && ((V[i]).order != (hyp_no_order ()))\n                            ~~~~~~~~~^~~~~~~ ./driver.pp.c:849:29-45 (cursor: 849:38)");
  update_cn_error_message_info("  let ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, 0u64);\n       ^./driver.pp.c:846:8:");
  cn_map* APs = map_create();
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(cn_bool_and(cn_bool_and(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, hyp_no_order()))), cn_bool_not(excluded(ex, i))))) {
        cn_pointer* a_13355 = cn_pointer_add_cn_bits_u64(ptr_phys_0, cn_bits_u64_multiply(i, cast_cn_bits_u64_to_cn_bits_u64(convert_to_cn_bits_u64(sizeof(char[4096])))));
        cn_map_set(APs, cast_cn_bits_u64_to_cn_integer(i), AllocatorPage(a_13355, convert_to_cn_bool(true), ((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, owned_enum));
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  cn_bool* a_13384 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        update_cn_error_message_info("  assert (each (u64 i; (start_i <= i) && (i < end_i))\n     ~~~~~~~~~~~^~~~~~~~~~~~~~~~~ ./driver.pp.c:852:6-34 (cursor: 852:17)");
        a_13384 = cn_bool_and(a_13384, vmemmap_wf(i, V, pool_l, P));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_13384);
  cn_bool* a_13430 = convert_to_cn_bool(true);
  {
    cn_bits_u64* i = cast_cn_bits_u64_to_cn_bits_u64(start_i);
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u64_le(start_i, i), cn_bits_u64_lt(i, end_i)))) {
      if (convert_from_cn_bool(cn_bool_and(cn_bool_and(cn_bits_u16_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->refcount, convert_to_cn_bits_u16(0)), cn_bool_not(cn_bits_u8_equality(((struct hyp_page_cn*) cn_map_get_struct_hyp_page_cn(V, cast_cn_bits_u64_to_cn_integer(i)))->order, hyp_no_order()))), cn_bool_not(excluded(ex, i))))) {
        update_cn_error_message_info("            && ((not (excluded (ex, i)))))\n     ~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:857:6-72 (cursor: 857:19)");
        a_13430 = cn_bool_and(a_13430, vmemmap_l_wf(i, physvirt_offset, virt_ptr, V, APs, pool_l, P, ex));
        cn_bits_u64_increment(i);
      }
      else {
        ;
      }
      cn_bits_u64_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_13430);
  cn_bool* a_13452 = convert_to_cn_bool(true);
  {
    cn_bits_u8* i = cast_cn_bits_u8_to_cn_bits_u8(convert_to_cn_bits_u8(0));
    while (convert_from_cn_bool(cn_bool_and(cn_bits_u8_le(convert_to_cn_bits_u8(0), i), cn_bits_u8_lt(i, P->max_order)))) {
      if (convert_from_cn_bool(convert_to_cn_bool(true))) {
        update_cn_error_message_info("  assert (each(u8 i; 0u8 <= i && i < P.max_order)\n               ~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ./driver.pp.c:859:16-86 (cursor: 859:33)");
        a_13452 = cn_bool_and(a_13452, freeArea_cell_wf(i, physvirt_offset, virt_ptr, V, APs, pool_l, P, ex));
        cn_bits_u8_increment(i);
      }
      else {
        ;
      }
      cn_bits_u8_increment(i);
    }
  }
  update_cn_error_message_info(NULL);
  cn_assert(a_13452);
  struct Hyp_pool_record* a_13461 = alloc(sizeof(struct Hyp_pool_record));
  a_13461->APs = APs;
  a_13461->pool = P;
  a_13461->vmemmap = V;
  return a_13461;
}

struct list_head_cn* O_struct_list_head(cn_pointer* p, cn_bool* condition, enum OWNERSHIP owned_enum)
{
  if (convert_from_cn_bool(condition)) {
    update_cn_error_message_info("unknown location");
    struct list_head_cn* v = owned_struct_list_head(p, owned_enum);
    return v;
  }
  else {
    update_cn_error_message_info("  else {\n           ~~~~~~~~~~~~~~~~~~~~~~~^~ ./driver.pp.c:873:12-37 (cursor: 873:35)");
    return todo_default_list_head();
  }
}
