DIR=$(dirname $0)

for f in $(find $DIR -name '*.ltz'); do
  $DIR/../check.sh $f || exit -2
done
