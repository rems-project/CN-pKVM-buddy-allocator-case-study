#define assert(x) ((void) 0)

void cn_print_nr_u64(int, unsigned long);

#include "page_alloc.c"

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
  hyp_physvirt_offset = 0x0;
  unsigned int nr_pages = 8;
  unsigned int reserved_pages = 0;
  u8 max_order = 10;

  void *start_virt = cn_aligned_alloc(PAGE_SIZE, PAGE_SIZE * nr_pages);
  phys_addr_t range_start = (phys_addr_t) __hyp_pa(start_virt);
  u64 pfn = hyp_phys_to_pfn(range_start);
  u64 npfn = 0-pfn;

  u64 vmemmap_size = sizeof(struct hyp_page) * nr_pages;
  void *start_of_owned_vmemmap = cn_malloc(vmemmap_size);
  __hyp_vmemmap = ((struct hyp_page *) start_of_owned_vmemmap) + npfn;


  struct hyp_pool *pool = cn_calloc(1, sizeof(struct hyp_pool));
  pool->range_start = range_start;
  pool->range_end = range_start + nr_pages * PAGE_SIZE;
  pool->max_order = max_order;

  hyp_pool_init(pool, hyp_phys_to_pfn(range_start), nr_pages, reserved_pages);

  return pool;
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
  struct hyp_pool *pool = init();

  void *page0 = hyp_alloc_pages(pool, 0);
  void *page1 = hyp_alloc_pages(pool, 0);
  /* void *page2 = hyp_alloc_pages(pool, 0); */
  /* void *page3 = hyp_alloc_pages(pool, 0); */
  /* void *page4 = hyp_alloc_pages(pool, 0); */
  /* void *page5 = hyp_alloc_pages(pool, 0); */
  /* void *page6 = hyp_alloc_pages(pool, 0); */
  /* void *page7 = hyp_alloc_pages(pool, 0); */

  /* cn_print_nr_u64 (0, page0?1:0); */
  /* cn_print_nr_u64 (1, page1?1:0); */
  /* cn_print_nr_u64 (2, page2?1:0); */
  /* cn_print_nr_u64 (3, page3?1:0); */
  /* cn_print_nr_u64 (4, page4?1:0); */
  /* cn_print_nr_u64 (5, page5?1:0); */
  /* cn_print_nr_u64 (6, page6?1:0); */
  /* cn_print_nr_u64 (7, page7?1:0); */

  /* ((char *)page0)[1234] = 1; */
  /* ((char *)page1)[1234] = 1; */
  /* ((char *)page2)[1234] = 1; */
  /* ((char *)page3)[1234] = 1; */
  /* ((char *)page4)[1234] = 1; */
  /* ((char *)page5)[1234] = 1; */
  /* ((char *)page6)[1234] = 1; */
  /* ((char *)page7)[1234] = 1; */

  hyp_put_page(pool, page0);
  hyp_put_page(pool, page1);
  /* hyp_put_page(pool, page2); */
  /* hyp_put_page(pool, page3); */
  /* hyp_put_page(pool, page4); */
  /* hyp_put_page(pool, page5); */
  /* hyp_put_page(pool, page6); */
  /* hyp_put_page(pool, page7); */

  /* void *page = hyp_alloc_pages(pool, 2); */

  return 0;
} 


