#!/bin/bash
$set BUILDERS_SRC
class=$1
package=${class%.*}
packagePath=$( echo $class | tr "." "/" )
echo $packagePath
rm impure_methods.txt
echo "RUN INFER IMPURITY ANALYZE"
echo "$BUILDERS_HOME/build/classes/"
echo "result"
pack="${packagePath%/*}"
infer run --impurity-only --no-default-checkers --no-default-linters -o $BE_EXP_SRC/inferFiles -- javac -cp lib/korat.jar:$BE_EXP_SRC/build/classes/ $BE_EXP_SRC/src/$pack/*.java
echo "$pack"

python3 resources/parseJSON.py
sed -i.tmp 's/\[/\\[/g' impure_methods.txt
sed -i.tmp 's/\]/\\]/g' impure_methods.txt
echo "END----RUN INFER IMPURITY ANALYZE"
sed -i -e 's/.$//' impure_methods.tmp
