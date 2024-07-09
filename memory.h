/* originally: ./arch/arm64/kvm/hyp/include/nvhe/memory.h */



/* SPDX-License-Identifier: GPL-2.0-only */
#ifndef __KVM_HYP_MEMORY_H
#define __KVM_HYP_MEMORY_H

/* #include <asm/kvm_mmu.h> */
/* #include <asm/page.h> */

/* #include <linux/types.h> */

/*
 * Accesses to struct hyp_page flags must be serialized by the host stage-2
 * page-table lock due to the lack of atomics at EL2.
 */
#define HOST_PAGE_NEED_POISONING    BIT(0)
#define HOST_PAGE_PENDING_RECLAIM    BIT(1)

struct hyp_pool;
struct hyp_page {
    unsigned short refcount;
    u8 order;
    u8 flags;
};

extern s64 hyp_physvirt_offset;
extern struct hyp_page *__hyp_vmemmap;
/*CN*/ extern void *cn_virt_base;
#define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap)

#define __hyp_pa(virt)    ((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(phys)    ((phys_addr_t)(phys) - hyp_physvirt_offset)

static inline void *hyp_phys_to_virt(phys_addr_t phys)
/*@ accesses hyp_physvirt_offset; cn_virt_base; @*/
/*@ requires let virt = phys - (u64) hyp_physvirt_offset; @*/
/*@ ensures {hyp_physvirt_offset} unchanged; @*/
/*@ ensures (u64) return == virt; @*/
{
    return CN_COPY_ALLOC_ID(__hyp_va(phys), cn_virt_base);
}

static inline phys_addr_t hyp_virt_to_phys(void *addr)
/*@ accesses hyp_physvirt_offset; @*/
/*@ requires let phys = cn__hyp_pa(hyp_physvirt_offset, addr); @*/
/*@ ensures {hyp_physvirt_offset} unchanged; @*/
/*@ ensures return == phys; @*/
{
    return __hyp_pa(addr);
}

enum {
  enum_PAGE_SHIFT = PAGE_SHIFT,
};

#define hyp_phys_to_pfn(phys)    ((phys) >> PAGE_SHIFT)
#define hyp_pfn_to_phys(pfn)    ((phys_addr_t)((pfn) << PAGE_SHIFT))
#define hyp_phys_to_page(phys)    (&hyp_vmemmap[hyp_phys_to_pfn(phys)])
#define hyp_virt_to_page(virt)    hyp_phys_to_page(__hyp_pa(virt))
#define hyp_virt_to_pfn(virt)    hyp_phys_to_pfn(__hyp_pa(virt))

#define hyp_page_to_pfn_macro(page)    ((struct hyp_page *)(page) - hyp_vmemmap)
#define hyp_page_to_phys(page)  hyp_pfn_to_phys((hyp_page_to_pfn(page)))
#define hyp_page_to_virt(page)    __hyp_va(hyp_page_to_phys(page))
#define hyp_page_to_pool(page)    (((struct hyp_page *)page)->pool)

/*@
function (u64) max_pfn ()
  { shift_right (0u64 - 1u64, (u64) enum_PAGE_SHIFT) }
@*/

static inline u64 hyp_page_to_pfn(struct hyp_page *page)
/*@ accesses __hyp_vmemmap; @*/
/*@ requires let offs = ((u64) page) - ((u64) __hyp_vmemmap); @*/
/*@ requires offs <= max_pfn () * (sizeof<struct hyp_page>); @*/
/*@ requires mod(offs, sizeof<struct hyp_page>) == 0u64; @*/
/*@ ensures return == offs / (sizeof<struct hyp_page>); @*/
/*@ ensures {__hyp_vmemmap} unchanged; @*/
{
  return hyp_page_to_pfn_macro(page);
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
    struct hyp_page *p = hyp_virt_to_page(addr);
    /*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
    /*CN*//*@extract Owned<struct hyp_page>, phys/(page_size()); @*/
    /* TODO originally: return p->refcount.  Introducing 'ret' here, so we can pack resources before returning; */
    int ret = p->refcount;

        return ret;
}

#define BUG_ON(condition) assert(!(condition))
#define USHRT_MAX ((unsigned short)~0U)

static inline void hyp_page_ref_inc(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount < (shift_left(1u16,16u16) - 1u16); @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == {(*p).refcount}@start + 1u16; @*/
{
    BUG_ON(p->refcount == USHRT_MAX);
    p->refcount++;
}

static inline void hyp_page_ref_dec(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount > 0u16; @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == {(*p).refcount}@start - 1u16; @*/
{
    BUG_ON(!p->refcount);
    p->refcount--;
}

static inline int hyp_page_ref_dec_and_test(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount > 0u16; @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == {(*p).refcount}@start - 1u16; @*/
/*@ ensures return == (((*p).refcount == 0u16) ? 1i32 : 0i32); @*/
{
    hyp_page_ref_dec(p);
    return (p->refcount == 0);
}

static inline void hyp_set_page_refcounted(struct hyp_page *p)
/*@ requires take O = Owned(p); @*/
/*@ requires (*p).refcount == 0u16; @*/
/*@ ensures take OR = Owned(p); @*/
/*@ ensures {(*p).order} unchanged; @*/
/*@ ensures (*p).refcount == 1u16; @*/
{
    BUG_ON(p->refcount);
    p->refcount = 1;
}
#endif /* __KVM_HYP_MEMORY_H */
