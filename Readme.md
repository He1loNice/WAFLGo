# WAFLGo: Critical Code Guided Directed Greybox Fuzzing for Commits
This research presents WAFLGo, a direct greybox fuzzer aimed at effectively discovering bugs introduced by commits. WAFLGo employs a novel critical code guided input generation strategy, enabling swift reaching commit change sites while thoroughly testing affected code. Additionally, we manually construct a dataset comprising 30 real-world bugs, with their corresponding bug-inducing commits identified.

# How to test with WAFLGo 
1) Install LLVM 12 with Gold-plugin and SVF-tools

Alternatively, you can use our provided [Docker image](https://hub.docker.com/repository/docker/he1lonice/waflgo), which comes with all the necessary dependencies pre-installed. This saves you the hassle of setting up the environment yourself.

2) Compile WAFLGo fuzzer
```bash
git clone https://github.com/He1loNice/WAFLGo.git /home/WAFLGo
cd /home/WAFLGo;make;cd llvm_mode;make;cd ../;cd instrument;cmake . ;make ;cd ../
```
3) Download subject (e.g., libjpeg-issue-493) 
```bash
# Clone subject repository
git clone https://github.com/libjpeg-turbo/libjpeg-turbo.git /home/waflgo-libjpeg
cd /home/waflgo-libjpeg; git checkout 88ae609 
```
4) Build binary 
```bash
export ADD="-g --notI "
export CC=/home/WAFLGo/afl-clang-fast CXX=/home/WAFLGo/afl-clang-fast++  CFLAGS="$ADD" CXXFLAGS="$ADD"
export AFL_CC=gclang AFL_CXX=gclang++

cmake . 
make clean;make -j $(nproc) 
unset AFL_CC AFL_CXX

# ** Get bitcode file from executable file

cp ./cjpeg-static ./
get-bc cjpeg-static 

# ** Set the target site

mkdir fuzz; cd fuzz
cp ../cjpeg-static.bc .

echo $'' > $TMP_DIR/BBtargets.txt
git diff HEAD^1 HEAD > ./commit.diff
cp /home/showlinenum.awk ./
sed -i -e 's/\r$//' showlinenum.awk
chmod +x showlinenum.awk
cat ./commit.diff |  ./showlinenum.awk show_header=0 path=1 | grep -e "\.[ch]:[0-9]*:+" -e "\.cpp:[0-9]*:+" -e "\.cc:[0-9]*:+" | cut -d+ -f1 | rev | cut -c2- | rev > ./targets

# cat ./targets

# ** Instrument

/home/WAFLGo/instrument/bin/cbi --targets=targets cjpeg-static.bc --stats=false
cp ./targets_id.txt /home
cp ./suffix.txt /home
cp ./targets*.txt /home
cp ./distance.txt /home
cp ./branch-distance.txt /home
cp ./branch-distance-min.txt /home
cp ./branch-curloc.txt /home
cp ./*_data.txt /home


# ** Compile bitcode file to executable file which is used to be fuzzed

/home/WAFLGo/afl-clang-fast++ cjpeg-static.ci.bc  -lstdc++  -o cjpeg-static.ci
cp ./bbinfo-fast.txt /home/bbinfo-ci-bc.txt
cp ./branch-distance-order.txt /home
cp ./*-distance-order.txt /home
cp ./*-order.txt /home
```
5) Start fuzzing
```
/home/WAFLGo/afl-fuzz  -T waflgo-libjpeg -t 1000+ -m none -z exp -c 45m -q 1 -i /home/jpg -o /home/out -- /home/waflgo-libjpeg/fuzz/cjpeg-static.ci  @@
```
