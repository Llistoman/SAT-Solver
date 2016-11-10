FILES=random3SAT/*

for f in $FILES
do
  echo "========================";
  echo $f;
  echo "";
  ./sat < $f;
  echo "========================";
  echo "";
done
echo "FINISHED";