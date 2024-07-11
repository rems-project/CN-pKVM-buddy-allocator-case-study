#include "page_alloc.c"

void *cn_aligned_alloc(size_t align, size_t size);


s64 hyp_physvirt_offset;


int main()
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_ptr; @*/
{

  s64 offset = PAGE_SIZE;
  unsigned int nr_pages = 20;
  unsigned int reserved_pages = 0;
  u8 max_order = 10;


  hyp_physvirt_offset = offset;
  __hyp_vmemmap = cn_aligned_alloc(sizeof(struct hyp_page), sizeof(struct hyp_page) * nr_pages);

  /* unsigned int i = 0; */
  /* while (i < nr_pages) { */
  /*   __hyp_vmemmap[i].refcount = 0; */
  /*   __hyp_vmemmap[i].order = 0; */
  /*   __hyp_vmemmap[i].flags = 0; */
  /*   i++; */
  /* } */


  void *start_virt = cn_aligned_alloc(PAGE_SIZE, PAGE_SIZE * nr_pages);

  phys_addr_t range_start = (phys_addr_t) __hyp_pa(start_virt);

  struct hyp_pool *pool = cn_aligned_alloc(sizeof(struct hyp_pool), sizeof(struct hyp_pool));
  *pool = (struct hyp_pool){ 0 };
  pool->range_start = range_start;
  pool->range_end = range_start + nr_pages * PAGE_SIZE;
  pool->max_order = max_order;



  hyp_pool_init(pool, hyp_phys_to_pfn(range_start), nr_pages, reserved_pages);


  return 0;
}



