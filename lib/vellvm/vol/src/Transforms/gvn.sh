#!/bin/bash

DIRS="../Interpreter/testcases/ ../Interpreter/testcases/llvm \
	../Interpreter/testcases/softbound/"
GVN="../_build/Transforms/main.native -gvn"
BC_DIR=./testcases/
OC_DIR=./testcases/olden-ccured/
OC_CASES="bh bisort em3d health mst perimeter power treeadd tsp"
S95_DIR=./testcases/spec95-ccured/
S95_CASES="129.compress 099.go 130.li 132.ijpeg"
PRE_OPT_FLAG="-disable-opt -raiseallocs -simplifycfg -domtree -domfrontier 
  -mem2reg 
  -globalopt -globaldce -ipconstprop -deadargelim -instcombine -simplifycfg 
  -basiccg -prune-eh -functionattrs -inline -simplify-libcalls -instcombine 
  -jump-threading -simplifycfg -domtree -domfrontier -scalarrepl -instcombine 
  -break-crit-edges -condprop -tailcallelim -simplifycfg -lowerswitch 
  -reassociate -domtree 
  -loops -loopsimplify -domfrontier -lcssa -loop-rotate -licm -lcssa 
  -loop-unswitch -instcombine -scalar-evolution -lcssa -iv-users -indvars 
  -loop-deletion -lcssa -loop-unroll -instcombine -lowerswitch -memdep"
SUF_OPT_FLAG="-disable-opt -memdep 
  -memcpyopt -sccp -instcombine -break-crit-edges -condprop -domtree -memdep -dse 
  -adce -simplifycfg -strip-dead-prototypes -print-used-types -deadtypeelim 
  -constmerge -preverify -domtree -verify"

PRE_LD_FLAG="-disable-opt -internalize -ipsccp -globalopt -constmerge 
  -deadargelim -instcombine -basiccg -inline -prune-eh -globalopt -globaldce 
  -basiccg -argpromotion -instcombine -jump-threading -domtree -domfrontier 
  -scalarrepl -basiccg -functionattrs -globalsmodref-aa -domtree -loops 
  -loopsimplify -domfrontier -licm -memdep"
SUF_LD_FLAG="-disable-opt -memdep -memcpyopt -dse -instcombine -jump-threading 
  -domtree -domfrontier -mem2reg -simplifycfg -globaldce -instcombine -simplifycfg 
  -adce -globaldce -preverify -domtree -verify"

OPT_FLAG="-disable-opt -raiseallocs -simplifycfg -domtree -domfrontier -mem2reg 
  -globalopt -globaldce -ipconstprop -deadargelim -instcombine -simplifycfg 
  -basiccg -prune-eh -functionattrs -inline -simplify-libcalls -instcombine 
  -jump-threading -simplifycfg -domtree -domfrontier -scalarrepl -instcombine 
  -break-crit-edges -condprop -tailcallelim -simplifycfg -reassociate -domtree 
  -loops -loopsimplify -domfrontier -lcssa -loop-rotate -licm -lcssa 
  -loop-unswitch -instcombine -scalar-evolution -lcssa -iv-users -indvars 
  -loop-deletion -lcssa -loop-unroll -instcombine -memdep 
  -gvn
  -memdep 
  -memcpyopt -sccp -instcombine -break-crit-edges -condprop -domtree -memdep -dse 
  -adce -simplifycfg -strip-dead-prototypes -print-used-types -deadtypeelim 
  -constmerge -preverify -domtree -verify"

NOGVN_OPT_FLAG="-disable-opt -raiseallocs -simplifycfg -domtree -domfrontier 
  -mem2reg 
  -globalopt -globaldce -ipconstprop -deadargelim -instcombine -simplifycfg 
  -basiccg -prune-eh -functionattrs -inline -simplify-libcalls -instcombine 
  -jump-threading -simplifycfg -domtree -domfrontier -scalarrepl -instcombine 
  -break-crit-edges -condprop -tailcallelim -simplifycfg -reassociate -domtree 
  -loops -loopsimplify -domfrontier -lcssa -loop-rotate -licm -lcssa 
  -loop-unswitch -instcombine -scalar-evolution -lcssa -iv-users -indvars 
  -loop-deletion -lcssa -loop-unroll -instcombine -memdep 
  -memdep 
  -memcpyopt -sccp -instcombine -break-crit-edges -condprop -domtree -memdep -dse 
  -adce -simplifycfg -strip-dead-prototypes -print-used-types -deadtypeelim 
  -constmerge -preverify -domtree -verify"

#LD_FLAG="-disable-opt -internalize -ipsccp -globalopt -constmerge 
#  -deadargelim -instcombine -basiccg -inline -prune-eh -globalopt -globaldce 
#  -basiccg -argpromotion -instcombine -jump-threading -domtree -domfrontier 
#  -scalarrepl -basiccg -functionattrs -globalsmodref-aa -domtree -loops 
#  -loopsimplify -domfrontier -licm -memdep
#  -gvn
#  -memdep -memcpyopt -dse -instcombine -jump-threading 
#  -domtree -domfrontier -mem2reg -simplifycfg -globaldce -instcombine -simplifycfg 
#  -adce -globaldce -preverify -domtree -verify"
LD_FLAG="-disable-opt"

AA_FLAG="-q -analyze -aa-meval -mprint-no-aliases -mprint-must-aliases -disable-output"

for name in ./testcases/*.ll; do 
  echo -e $name": \c"  
  llvm-as -f $name -o input.bc
  opt $AA_FLAG input.bc >& aa.db
  $GVN input.bc
  $GVN input.bc >& output.ll
  llvm-as -f output.ll
  llvm-ld output.bc -o test.exe
  time ./test.exe
done;
for dir in $DIRS; do
  for name in $dir/*.ll; do 
    echo -e $name": \c"  
    llvm-as -f $name -o input.bc
    opt $AA_FLAG input.bc >& aa.db
    $GVN input.bc >& output.ll
    llvm-as -f output.ll
    llvm-ld -disable-opt output.bc -o test.exe
    time ./test.exe
  done;
done;

for name in $OC_CASES; do 
  echo -e $name": \c" ; 

  echo -e "LLVM a0"; time opt $PRE_OPT_FLAG $OC_DIR$name"/test.bc" -f -o opt.bc
  echo -e "AA"; time opt $AA_FLAG opt.bc >& aa.db
  du -h aa.db
  #echo -e "Coq GVN"; time $GVN opt.bc |& sed '2itarget triple = "i386-unknown-linux-gnu"' >& $name"o.ll"
  echo -e "Coq GVN"; time $GVN opt.bc >& $name"o.ll"
  llvm-as -f $name"o.ll" -o $name"o.bc"
  echo -e "LLVM a1"; time opt $SUF_OPT_FLAG $name"o.bc" -f -o opt.bc
  echo -e "LLVM a2"; time llvm-ld -native -lm $LD_FLAG opt.bc -o $name"a.exe"

  echo -e "LLVM b1"; time opt $OPT_FLAG $OC_DIR$name"/test.bc" -f -o opt.bc
  echo -e "LLVM b2"; time llvm-ld -native -lm $LD_FLAG opt.bc -o $name"b.exe"

  echo -e "LLVM c1"; time opt $NOGVN_OPT_FLAG $OC_DIR$name"/test.bc" -f -o opt.bc
  echo -e "LLVM c2"; time llvm-ld -native -lm $LD_FLAG opt.bc -o $name"c.exe"
done;
echo -e "bh b: \c"; time ./bhb.exe < ./testcases/olden-ccured/bh/slow_input >& /dev/null;
echo -e "bh a: \c"; time ./bha.exe < ./testcases/olden-ccured/bh/slow_input >& /dev/null;
echo -e "bh c: \c"; time ./bhc.exe < ./testcases/olden-ccured/bh/slow_input >& /dev/null;
echo -e "bisort b: \c"; time ./bisortb.exe 5000000 0 >& /dev/null;
echo -e "bisort a: \c"; time ./bisorta.exe 5000000 0 >& /dev/null;
echo -e "bisort c: \c"; time ./bisortc.exe 5000000 0 >& /dev/null;
echo -e "em3d b: \c"; time ./em3db.exe 30000 300 50 >& /dev/null;
echo -e "em3d a: \c"; time ./em3da.exe 30000 300 50 >& /dev/null;
echo -e "em3d c: \c"; time ./em3dc.exe 30000 300 50 >& /dev/null;
echo -e "health b: \c"; time ./healthb.exe 8 250 1 >& /dev/null;
echo -e "health a: \c"; time ./healtha.exe 8 250 1 >& /dev/null;
echo -e "health c: \c"; time ./healthc.exe 8 250 1 >& /dev/null;
echo -e "mst b: \c"; time ./mstb.exe 4000 >& /dev/null;
echo -e "mst a: \c"; time ./msta.exe 4000 >& /dev/null;
echo -e "mst c: \c"; time ./mstc.exe 4000 >& /dev/null;
echo -e "perimeter b: \c"; time ./perimeterb.exe 12 2000 >& /dev/null;
echo -e "perimeter a: \c"; time ./perimetera.exe 12 2000 >& /dev/null;
echo -e "perimeter c: \c"; time ./perimeterc.exe 12 2000 >& /dev/null;
echo -e "power b: \c"; time ./powerb.exe >& /dev/null;
echo -e "power a: \c"; time ./powera.exe >& /dev/null;
echo -e "power c: \c"; time ./powerc.exe >& /dev/null;
echo -e "treeadd b: \c"; time ./treeaddb.exe 24 10 >& /dev/null; 
echo -e "treeadd a: \c"; time ./treeadda.exe 24 10 >& /dev/null; 
echo -e "treeadd c: \c"; time ./treeaddc.exe 24 10 >& /dev/null; 
echo -e "tsp b: \c"; time ./tspb.exe 2000000 0 >& /dev/null;
echo -e "tsp a: \c"; time ./tspa.exe 2000000 0 >& /dev/null;
echo -e "tsp c: \c"; time ./tspc.exe 2000000 0 >& /dev/null;
for name in $S95_CASES; do 
  echo -e $name": \c" ; 

  echo -e "LLVM a0"; time opt $PRE_OPT_FLAG $S95_DIR$name"/src/test.bc" -f -o opt.bc
  echo -e "AA"; time opt $AA_FLAG opt.bc >& aa.db
  du -h aa.db
  #echo -e "Coq GVN"; time $GVN opt.bc |& sed '2itarget triple = "i386-unknown-linux-gnu"' >& $name"o.ll"
  echo -e "Coq GVN"; time $GVN opt.bc >& $name"o.ll"
  llvm-as -f $name"o.ll" -o $name"o.bc"
  echo -e "LLVM a1"; time opt $SUF_OPT_FLAG $name"o.bc" -f -o opt.bc
  echo -e "LLVM a2"; time llvm-ld -native -lm $LD_FLAG opt.bc -o $name"a.exe"

  echo -e "LLVM b1"; time opt $OPT_FLAG $S95_DIR$name"/src/test.bc" -f -o opt.bc
  echo -e "LLVM b2"; time llvm-ld -native -lm $LD_FLAG opt.bc -o $name"b.exe"

  echo -e "LLVM c1"; time opt $NOGVN_OPT_FLAG $S95_DIR$name"/src/test.bc" -f -o opt.bc
  echo -e "LLVM c2"; time llvm-ld -native -lm $LD_FLAG opt.bc -o $name"c.exe"
done;
echo -e "099.go b: \c"; time ./099.gob.exe 100 15 >& /dev/null
echo -e "099.go a: \c"; time ./099.goa.exe 100 15 >& /dev/null
echo -e "099.go c: \c"; time ./099.goc.exe 100 15 >& /dev/null
#echo -e "130.li: \c"; time ./130.li.exe ./testcases/spec95-ccured/130.li/src/ref.lsp;
echo -e "129.compress b: \c"; time ./129.compressb.exe < ./testcases/spec95-ccured/129.compress/src/slow_input.data >& /dev/null
echo -e "129.compress a: \c"; time ./129.compressa.exe < ./testcases/spec95-ccured/129.compress/src/slow_input.data >& /dev/null
echo -e "129.compress c: \c"; time ./129.compressc.exe < ./testcases/spec95-ccured/129.compress/src/slow_input.data >& /dev/null
echo -e "132.ijpeg b: \c"; time ./132.ijpegb.exe -image_file testcases/spec95-ccured/132.ijpeg/data/ref/input/vigo.ppm -compression.quality 90 -compression.optimize_coding 0 -compression.smoothing_factor 90 -difference.image 1 -difference.x_stride 10 -difference.y_stride 10 -verbose 1 -GO.findoptcomp >& /dev/null
echo -e "132.ijpeg a: \c"; time ./132.ijpega.exe -image_file testcases/spec95-ccured/132.ijpeg/data/ref/input/vigo.ppm -compression.quality 90 -compression.optimize_coding 0 -compression.smoothing_factor 90 -difference.image 1 -difference.x_stride 10 -difference.y_stride 10 -verbose 1 -GO.findoptcomp >& /dev/null
echo -e "132.ijpeg c: \c"; time ./132.ijpegc.exe -image_file testcases/spec95-ccured/132.ijpeg/data/ref/input/vigo.ppm -compression.quality 90 -compression.optimize_coding 0 -compression.smoothing_factor 90 -difference.image 1 -difference.x_stride 10 -difference.y_stride 10 -verbose 1 -GO.findoptcomp >& /dev/null
rm -f bisort* em3d* health* mst* treeadd* 129.compress* test-softbound.bc \
  130.li* 099.go* tsp* bh* power* perimeter* 132.ijpeg* opt.bc input.* output.* \
  test.exe test.exe.bc aa.db


