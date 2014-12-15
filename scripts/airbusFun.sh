function header() {
	echo
	echo "##### $1 #####"
}
set -o errexit
set -o pipefail # otherwise tee will always succeed, even if goblint has a non-zero exit status
pedantic=false
export OCAMLRUNPARAM=b
export scrambled=true
ret=${1-"success"}
if [ $ret = "success" ]; then
    options="--enable ana.arinc.assume_success"
else
    options="--disable ana.arinc.assume_success"
    ret="fail"
fi
analyzer=~/analyzer
inputs=~/Dropbox/airbus
input=unrolled_monit.c
conf=ab.conf
if [ `pwd` = $analyzer ]; then
    echo "Do not run in $analyzer! Go somewhere else; the goblint binary will be copied."
    exit 1
fi
function git_dirty {
    dir=${1-"`pwd`"};
    test -n "$(git -C $dir  status --porcelain)"
}
if $pedantic && git_dirty "$analyzer"; then
    echo "The repo $analyzer is not in a clean state. Abort!"
    exit 1
fi
commit=$(git -C $analyzer rev-parse --short HEAD)
date=$(git -C $analyzer show -s --pretty=format:"%ai" $commit | sed 's/ +.*//' | sed 's/ /_/g')
lastmod=$(find $analyzer/{src,scripts} -printf "%Tm-%Td-%TT\n" | sort -nr | head -n 1 | cut -d. -f1)
result="result_${date}_${commit}_${lastmod}_${ret}"
if [ -e $result ]; then
    echo "$result already exists!"
    exit
fi
echo "results will be in $result"
mkdir -p $result && cd $result

mkdir -p result
header "Building & copying files from $analyzer"
pushd $analyzer && make nat && popd
cp -f $analyzer/goblint .
cp -f $analyzer/spin/arinc?base.pml result # copy everything before the long running stuff...
header "Copying input & config from $inputs"
cp -f $inputs/{$input,$conf} .
if [ "$2" = "init" ]; then
    exit 0
fi
dbg="--enable colors --enable dbg.debug --enable dbg.verbose --trace arinc --disable ana.arinc.debug_pml"
goblint="./goblint --conf $conf --set ana.activated[0] ['base','arinc'] $dbg --enable noverify --enable ana.arinc.export $options"
header "Write effective config"
$goblint --writeconf all.conf
header "Starting goblint"
/bin/time -v -o time.fun.txt $goblint $input 2>&1 | tee trace.fun.txt
cat time.fun.txt
dot="result/arinc.dot"
pml="result/arinc.pml"
echo "$dot has $(wc -l < $dot) lines!"
echo "$pml has $(wc -l < $pml) lines!"
# fdp -Tpng -O $dot
# gnome-open ${dot}.png

pushd result
header "Generating SPIN Verifier from Promela Code"
set +o errexit # we want to be able to abort this if it takes too long
/bin/time -v -o time.spin.txt spin -DPRIOS -a arinc.pml 2>&1 | tee trace.spin.txt
set -o errexit
cat time.spin.txt
clang -DVECTORSZ=5000 -o pan pan.c # complained that VECTORSZ should be > 1280
echo "Verify! If there are errors, this will generate a file arinc.pml.trail"
./pan -n -a || (echo "Verification failed! Do simulation guided by trail."; spin -g -l -p -r -s -t -X -u10000 arinc.pml)
popd # result
popd # script dir
unset scrambled