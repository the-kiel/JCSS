n=$1
l=$2
inputFile="../../prefixes/opt/pref_opt"$n".txt"
numRows=$(wc -l $inputFile | awk ' { print $1  } ')
echo "have "$numRows" rows to test! "
for i in `seq 0 $numRows`; do 
 outFile="out_"$n"_"$l"_"$i".txt"
./minisat -input-Bits=$n -betterEncoding -layers=$l -splitter -no-lastLayerConstraints  -fixFirst -usePrefFile -prefFile=$inputFile  -useSomeValues -shrink=2 -row=$i > $outFile
if [ $(grep UNSAT $outFile | wc -l | awk ' { print $1 } ') -le 0 ] ; then 
    echo $outFile
fi
done 
