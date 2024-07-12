rm -rf build/
mkdir build
clang-18 -E -P -CC driver.c > driver.pp.c
cn ./driver.pp.c --output_decorated=driver.pp.exec.c --output_decorated_dir=build/ --with_ownership_checking --copy_source_dir
clang-18 -g -O0 -std=gnu11 -I$OPAM_SWITCH_PREFIX/lib/cn/runtime/include  $OPAM_SWITCH_PREFIX/lib/cn/runtime/libcn.a build/driver.pp.exec.c build/cn.c -o build/driver.exec.o
