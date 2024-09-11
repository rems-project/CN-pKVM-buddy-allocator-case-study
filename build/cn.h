#ifndef CN_HEADER
#define CN_HEADER
#include <cn-executable/utils.h>




/* ORIGINAL C STRUCTS */

struct list_head {
  struct list_head* next;
  struct list_head* prev;
};

struct hyp_pool {
  struct list_head free_area[11];
  unsigned long long range_start;
  unsigned long long range_end;
  unsigned char max_order;
};

struct hyp_page {
  unsigned short refcount;
  unsigned char order;
  unsigned char flags;
};



/* CN VERSIONS OF C STRUCTS */

struct list_head_cn {
  cn_pointer* next;
  cn_pointer* prev;
};

struct hyp_pool_cn {
  cn_map* free_area;
  cn_bits_u64* range_start;
  cn_bits_u64* range_end;
  cn_bits_u8* max_order;
};

struct hyp_page_cn {
  cn_bits_u16* refcount;
  cn_bits_u8* order;
  cn_bits_u8* flags;
};



struct exclude_none_record {
  cn_bool* any;
  cn_bool* do_ex1;
  cn_bool* do_ex2;
  cn_bits_u64* ex1;
  cn_bits_u64* ex2;
};
struct exclude_one_record {
  cn_bool* any;
  cn_bool* do_ex1;
  cn_bool* do_ex2;
  cn_bits_u64* ex1;
  cn_bits_u64* ex2;
};
struct exclude_two_record {
  cn_bool* any;
  cn_bool* do_ex1;
  cn_bool* do_ex2;
  cn_bits_u64* ex1;
  cn_bits_u64* ex2;
};

struct Hyp_pool_ex1_record {
  cn_map* APs;
  struct hyp_pool_cn* pool;
  cn_map* vmemmap;
};
struct Hyp_pool_ex2_record {
  cn_map* APs;
  struct hyp_pool_cn* pool;
  cn_map* vmemmap;
};
struct Hyp_pool_record {
  cn_map* APs;
  struct hyp_pool_cn* pool;
  cn_map* vmemmap;
};


/* CN DATATYPES */





/* OWNERSHIP FUNCTIONS */


struct list_head_cn* owned_struct_list_head(cn_pointer*, enum OWNERSHIP);

struct hyp_page_cn* owned_struct_hyp_page(cn_pointer*, enum OWNERSHIP);

struct hyp_pool_cn* owned_struct_hyp_pool(cn_pointer*, enum OWNERSHIP);

cn_bits_u8* owned_char(cn_pointer*, enum OWNERSHIP);

cn_pointer* owned_void_pointer(cn_pointer*, enum OWNERSHIP);

cn_bits_i64* owned_signed_long_long(cn_pointer*, enum OWNERSHIP);

cn_pointer* owned_struct_hyp_page_pointer(cn_pointer*, enum OWNERSHIP);


/* GENERATED STRUCT FUNCTIONS */

struct list_head_cn* convert_to_struct_list_head_cn(struct list_head);

struct hyp_pool_cn* convert_to_struct_hyp_pool_cn(struct hyp_pool);

struct hyp_page_cn* convert_to_struct_hyp_page_cn(struct hyp_page);

cn_bool* struct_list_head_cn_equality(void*, void*);

cn_bool* struct_hyp_pool_cn_equality(void*, void*);

cn_bool* struct_hyp_page_cn_equality(void*, void*);

void* cn_map_get_struct_list_head_cn(cn_map*, cn_integer*);

void* cn_map_get_struct_hyp_pool_cn(cn_map*, cn_integer*);

void* cn_map_get_struct_hyp_page_cn(cn_map*, cn_integer*);

struct list_head_cn* default_struct_list_head_cn();

struct hyp_pool_cn* default_struct_hyp_pool_cn();

struct hyp_page_cn* default_struct_hyp_page_cn();

cn_bool* struct_exclude_none_record_equality(void*, void*);
cn_bool* struct_exclude_one_record_equality(void*, void*);
cn_bool* struct_exclude_two_record_equality(void*, void*);
cn_bool* struct_Hyp_pool_ex1_record_equality(void*, void*);
cn_bool* struct_Hyp_pool_ex2_record_equality(void*, void*);
cn_bool* struct_Hyp_pool_record_equality(void*, void*);
struct exclude_none_record* default_struct_exclude_none_record();
struct exclude_one_record* default_struct_exclude_one_record();
struct exclude_two_record* default_struct_exclude_two_record();
struct Hyp_pool_ex1_record* default_struct_Hyp_pool_ex1_record();
struct Hyp_pool_ex2_record* default_struct_Hyp_pool_ex2_record();
struct Hyp_pool_record* default_struct_Hyp_pool_record();
void* cn_map_get_struct_exclude_none_record(cn_map*, cn_integer*);
void* cn_map_get_struct_exclude_one_record(cn_map*, cn_integer*);
void* cn_map_get_struct_exclude_two_record(cn_map*, cn_integer*);
void* cn_map_get_struct_Hyp_pool_ex1_record(cn_map*, cn_integer*);
void* cn_map_get_struct_Hyp_pool_ex2_record(cn_map*, cn_integer*);
void* cn_map_get_struct_Hyp_pool_record(cn_map*, cn_integer*);

/* CN FUNCTIONS */

cn_bits_u64* max_pfn();
cn_pointer* copy_alloc_id_cn(cn_bits_u64*, cn_pointer*);
cn_bits_u64* page_size();
cn_bits_u8* max_order();
cn_bits_u8* hyp_no_order();
cn_bits_u64* cn_hyp_page_to_pfn(cn_pointer*, cn_pointer*);
cn_bits_u64* cn__hyp_pa(cn_bits_i64*, cn_pointer*);
cn_bits_u64* cn_hyp_phys_to_pfn(cn_bits_u64*);
cn_bits_u64* cn_hyp_virt_to_pfn(cn_bits_i64*, cn_pointer*);
cn_bits_u64* cn_hyp_pfn_to_phys(cn_bits_u64*);
cn_bits_u64* cn_hyp_page_to_phys(cn_pointer*, cn_pointer*);
cn_pointer* cn__hyp_va(cn_pointer*, cn_bits_i64*, cn_bits_u64*);
cn_pointer* cn_hyp_page_to_virt(cn_pointer*, cn_bits_i64*, cn_pointer*, cn_pointer*);
cn_bits_u64* calc_buddy(cn_bits_u64*, cn_bits_u8*);
cn_bits_u64* pfn_buddy(cn_bits_u64*, cn_bits_u8*);
cn_bool* order_aligned(cn_bits_u64*, cn_bits_u8*);
cn_bits_u64* order_align(cn_bits_u64*, cn_bits_u8*);
cn_bool* cellPointer(cn_pointer*, cn_bits_u64*, cn_bits_u64*, cn_bits_u64*, cn_pointer*);
cn_bits_u64* page_size_of_order(cn_bits_u8*);
cn_bool* page_aligned(cn_bits_u64*, cn_bits_u8*);
cn_bool* excluded(struct exclude_two_record*, cn_bits_u64*);
struct exclude_none_record* exclude_none();
struct exclude_one_record* exclude_one(cn_bits_u64*);
struct exclude_two_record* exclude_two(cn_bits_u64*, cn_bits_u64*);
cn_bool* vmemmap_good_pointer(cn_bits_i64*, cn_pointer*, cn_map*, cn_bits_u64*, cn_bits_u64*, struct exclude_two_record*);
cn_bool* page_group_ok(cn_bits_u64*, cn_map*, struct hyp_pool_cn*);
cn_bool* init_vmemmap_page(cn_bits_u64*, cn_map*, cn_pointer*, struct hyp_pool_cn*);
cn_bool* vmemmap_normal_order_wf(cn_bits_u64*, struct hyp_page_cn*, struct hyp_pool_cn*);
cn_bool* vmemmap_wf(cn_bits_u64*, cn_map*, cn_pointer*, struct hyp_pool_cn*);
cn_bool* vmemmap_l_wf(cn_bits_u64*, cn_bits_i64*, cn_pointer*, cn_map*, cn_map*, cn_pointer*, struct hyp_pool_cn*, struct exclude_two_record*);
cn_bool* freeArea_cell_wf(cn_bits_u8*, cn_bits_i64*, cn_pointer*, cn_map*, cn_map*, cn_pointer*, struct hyp_pool_cn*, struct exclude_two_record*);
cn_bool* hyp_pool_wf(cn_pointer*, struct hyp_pool_cn*, cn_pointer*, cn_bits_i64*);
cn_bits_u8* get_order_uf(cn_bits_u64*);
cn_pointer* virt(cn_pointer*, cn_bits_i64*);
struct list_head_cn* todo_default_list_head();


void Byte(cn_pointer*, enum OWNERSHIP);
void ByteV(cn_pointer*, cn_bits_u8*, enum OWNERSHIP);
void Page(cn_pointer*, cn_bool*, cn_bits_u8*, enum OWNERSHIP);
void ZeroPage(cn_pointer*, cn_bool*, cn_bits_u8*, enum OWNERSHIP);
void AllocatorPageZeroPart(cn_pointer*, cn_bits_u8*, enum OWNERSHIP);
struct list_head_cn* AllocatorPage(cn_pointer*, cn_bool*, cn_bits_u8*, enum OWNERSHIP);
struct Hyp_pool_ex1_record* Hyp_pool_ex1(cn_pointer*, cn_pointer*, cn_pointer*, cn_bits_i64*, cn_bits_u64*, enum OWNERSHIP);
struct Hyp_pool_ex2_record* Hyp_pool_ex2(cn_pointer*, cn_pointer*, cn_pointer*, cn_bits_i64*, cn_bits_u64*, cn_bits_u64*, enum OWNERSHIP);
struct Hyp_pool_record* Hyp_pool(cn_pointer*, cn_pointer*, cn_pointer*, cn_bits_i64*, enum OWNERSHIP);
struct list_head_cn* O_struct_list_head(cn_pointer*, cn_bool*, enum OWNERSHIP);
#endif