rm -rf build/
mkdir build
clang-18 -E -P -CC page_alloc.c > page_alloc.pp.c
cn page_alloc.pp.c --output_decorated=page_alloc.pp.exec.c --output_decorated_dir=build/ --with_ownership_checking --copy_source_dir
clang-18 -I$OPAM_SWITCH_PREFIX/lib/cn/runtime/include  $OPAM_SWITCH_PREFIX/lib/cn/runtime/libcn.a build/page_alloc.pp.exec.c build/cn.c
