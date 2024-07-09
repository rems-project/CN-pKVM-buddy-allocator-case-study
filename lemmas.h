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
