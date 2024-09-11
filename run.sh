rm -rf build/
mkdir build
clang-18 -E -P -CC driver.c > driver.pp.c
cn instrument ./driver.pp.c --output-decorated=driver.pp.exec.c --output-decorated-dir=build/ --with-ownership-checking
clang-18 -g -O0 -std=gnu11 -I$OPAM_SWITCH_PREFIX/lib/cn/runtime/include  $OPAM_SWITCH_PREFIX/lib/cn/runtime/libcn.a build/driver.pp.exec.c build/cn.c -o build/driver.exec.o
