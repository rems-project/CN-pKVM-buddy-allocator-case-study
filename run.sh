# rm -rf build/
# mkdir build
cc -E -P -CC driver.c > driver.pp.c
cn instrument ./driver.pp.c --output-decorated=driver.pp.exec.c --output-decorated-dir=build/
echo "Compiling..."
cc -g -c -O0 -std=gnu11 -I$OPAM_SWITCH_PREFIX/lib/cn/runtime/include build/driver.pp.exec.c build/cn.c
echo "Linking..."
cc -I$OPAM_SWITCH_PREFIX/lib/cn/runtime/include -o build/driver.exec.o ./*.o $OPAM_SWITCH_PREFIX/lib/cn/runtime/libcn.a
./build/driver.exec.o
echo "Done!"