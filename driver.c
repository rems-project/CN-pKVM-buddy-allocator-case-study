#include "page_alloc.c"

void *aligned_malloc(size_t align, size_t size);



void cn_assume_ownership(void *generic_c_ptr, size_t size, char *fun);

void *cn_aligned_malloc(size_t align, size_t size) 
{
  void *p = aligned_malloc(align, size);
  char str[] = "cn_aligned_malloc";
  cn_assume_ownership((void*) p, size, str);
  return p;
}


s64 hyp_physvirt_offset;


void *malloc_hyp_page(unsigned int nr) 
/* trusted;
   requires nr > 0u32;
   ensures mod ((u64) return, sizeof<struct hyp_page>) == 0u64;
           take V = each (u64 i; 0u64 <= i && i < (u64) nr)
                    {Block<struct hyp_page>(array_shift<struct hyp_page>(return, i)) };
*/
{
  return aligned_malloc(sizeof(struct hyp_page), 
                        sizeof(struct hyp_page) * nr);
}

void *malloc_init_hyp_page(unsigned int nr)
/* requires nr > 0u32;
   ensures mod ((u64) return, sizeof<struct hyp_page>) == 0u64;
           take V = each (u64 i; 0u64 <= i && i < (u64) nr)
                    {Owned<struct hyp_page>(array_shift<struct hyp_page>(return, i)) };
*/
{
  struct hyp_page* p = (struct hyp_page *) malloc_hyp_page(nr);

  for (unsigned int i = 0; i < nr; i++) 
  /* 
  inv {nr} unchanged;
      0u32 <= i; i <= nr;
      mod ((u64) p, sizeof<struct hyp_page>) == 0u64;            
      take V1 = each (u64 j; 0u64 <= j && j < (u64) i)
                     {Owned<struct hyp_page>(array_shift<struct hyp_page>(p, j)) }; 
      take V2 = each (u64 j; (u64) i <= j && j < (u64) nr)
                     {Block<struct hyp_page>(array_shift<struct hyp_page>(p, j)) }; 
  */
  {
    /* extract Block<struct hyp_page>, (u64) i; */
    /* extract Owned<struct hyp_page>, (u64) i; */
    p[i].refcount = 0;
    p[i].order = 0;
    p[i].flags = 0;
  }

  return p;

}


void *malloc_pages(unsigned int nr_pages)
/* trusted;
    accesses hyp_physvirt_offset; cn_virt_ptr;
    requires nr_pages > 0u32;
             let ptr_phys_0 = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, 0u64);
    ensures let start = cn__hyp_pa(hyp_physvirt_offset, return);
            mod (start, page_size ()) == 0u64;
            let start_i = start / page_size ();
            take P = each (u64 i; start_i <= i && i < start_i + (u64) nr_pages)
                          { Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), true, 0u8) }; 
*/
{
  return aligned_malloc(PAGE_SIZE, PAGE_SIZE * nr_pages);
}


void setup(s64 offset, 
           unsigned int nr_pages, 
           unsigned int reserved_pages,
           u8 max_order)
/* accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_ptr; */
{
  hyp_physvirt_offset = offset;
  __hyp_vmemmap = malloc_init_hyp_page(nr_pages);
  void *start_virt = malloc_pages(nr_pages);

  /* void* ptr_phys_0 = (void*) __hyp_va(0); */

  phys_addr_t range_start = (phys_addr_t) __hyp_pa(start_virt);

  struct hyp_pool poolv = { 0 };
  poolv.range_start = range_start;
  poolv.range_end = range_start + nr_pages * PAGE_SIZE;
  poolv.max_order = max_order;

  /* printf("Running hyp_pool_init"); */
  hyp_pool_init(&poolv, hyp_phys_to_pfn(range_start), nr_pages, reserved_pages);
  /* printf("Done."); */
}


int main () {
  setup(PAGE_SIZE, 20, 0, 10);
  return 0;
}
