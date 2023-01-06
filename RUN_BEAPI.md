# Running `BEAPI` on your own case study

To run `BEAPI` on your case study follow the steps below.

## 1. Get the source code of your class and compile it

To demonstrate the use of `BEAPI` on a custom class we randomly selected a [repository of data structure implementations from Github](https://github.com/anthonynsimon/java-ds-algorithms).

Make a folder named `<folder>` inside `$BE_EXP_SRC` for your project, and clone the repo in there. We already cloned the repo in folder `$BE_EXP_SRC/5_github`.

For the provided scripts to work we require that the source code is stored in:

```
$BE_EXP_SRC/<folder>/src/main/java
```

and the classes are compiled to folder:

```
$BE_EXP_SRC/<folder>/build/classes
```

For simplicity, we made an `ant` build file to easily compile the code and complies with the required folder structure. To compile the code run the following commands: 

```
cd $BE_EXP_SRC/5_github
ant compile
```

We'll assume the class you want to run `BEAPI` on is:

```
$BE_EXP_SRC/5_github/src/main/java/com/anthonynsimon/datastructures/MultiStackArray.java
```

The binary for this class will be located in:

```
$BE_EXP_SRC/5_github/build/classes/com/anthonynsimon/datastructures/MultiStackArray.class
```

## 2. Select (or define new) `BEAPI` configuration files

### Scope Definition for Primitive Types

The current `BEAPI` implementation requires the user to provide the primitive type values that will be used as parameters of API methods in a "literals" file. We provide predefined literal files for scopes from 1 to 15 (that is, from one and up to fifteen integers, respectively), in folder `$BE_EXP_SRC/scripts/literals/`.

In our example, we'll use the literals file for scope 3 (3 integers). The contents of this file are shown below:

```
# cat $BE_EXP_SRC/scripts/literals/literals3.txt

START CLASSLITERALS
CLASSNAME
java.lang.Integer
LITERALS
int:0
int:1
int:2
END CLASSLITERALS
```

The format of the literals file is inherited from [Randoop](https://randoop.github.io/randoop/). In the example above, we specify the range of integers that `BEAPI` will use. One could also specify domains for other primitive types like floats, doubles or strings if needed.

### Scope Definition for Reference Types

The current `BEAPI` implementation also requires the user to provide the maximum number of different objects (reachable from the root) that a structure is allowed to have (see Section 3.1), and the fields that will be employed for object canonicalization (see Section 3.2). Predefined configuration files for scopes from 1 to 15 (that is, from one and up to fifteen maximum objects, respectively) are given in folder `$BE_EXP_SRC/scripts/properties/`.

In our example, we'll use the configuration file (in the typical Java properties format) for scope 3 (3 integers). The contents of this file are shown below:

```
% cat $BE_EXP_SRC/scripts/properties/scope3.all.canonicalizer.properties 

max.objects=3
max.array.objects=3
save.array.null=true
omit.fields=modCount|ALLOWED_IMBALANCE
```

The `max.objects` parameter specifies the maximum number of objects allowed (for any class); `max.array.objects` is the maximum number of arrays values to be canonicalized; `save.array.null` indicates whether null values in arrays must be included in canonicalization; `omit.fields` is a Java regular expresion that indicates the fields that must be omitted in canonicalization of objects (see Section 3.2; this is not needed in our example and could be removed without changing the results). Test sequences that create a structure containing a larger number of different objects (of any class) than `max.objects` will be discarded (and the structure too). 

## 3. (Optional) Run automated builders identification

**Note**: Builders identification is not always deterministic and the results may vary slightly in some runs. To easily reproduce this experiment we precomputed and stored the above builders file in: 

```$BE_EXP_SRC/scripts/config/5_github/builders/com.anthonynsimon.datastructures.MultiStackArray```

Builders for `BEAPI` can also be provided manually.

To run automated builders identification first move to the scripts folder:

```
cd $BE_EXP_SRC/scripts
```

To automatically identify builders for this case study, you can run the script:

```
./run-builder-identification-beapi.sh <folder> <case study> <literals> <configuration>
```

where `<folder>` is the folder within `$BE_EXP_SRC` that includes the source code of the case study; `<case study>` is one of the case studies inside `<folder>` ; `<literals>` is a literals file (see [Scope Definition for Primitive Types](#Scope-Definition-for-Primitive-Types));`<configuration>` is a configuration file (see [Scope Definition for Reference Types](#Scope-Definition-for-Reference-Types)).

In our example:

```
./run-builder-identification-beapi.sh 5_github com.anthonynsimon.datastructures.MultiStackArray literals/literals5.txt properties/scope5.all.canonicalizer.properties 
```

The identified builders are saved in `$BE_EXP_SRC/scripts/results-builders/<folder>/<case study>/builders.txt`. In our example:

```
% cat results-builders/5_github/com.anthonynsimon.datastructures.MultiStackArray/builders.txt

com.anthonynsimon.datastructures.MultiStackArray.<init>\(int,int\)
com.anthonynsimon.datastructures.MultiStackArray.push\(int,java.lang.Object\)
``` 

## 4. Generate tests using `BEAPI` 

We are ready to run `BEAPI` to generate a JUnit bounded exhaustive test suite for our case study. For this, run the following script: 

```
./run-beapi.sh <folder> <case study> <literals> <configuration> <builders>
```

where `<folder>` is the folder within `$BE_EXP_SRC` that includes the source code of the case study; `<case study>` is one of the case studies inside `<folder>` ; `<literals>` is a literals file (see [Scope Definition for Primitive Types](#Scope-Definition-for-Primitive-Types));`<configuration>` is a configuration file (see [Scope Definition for Reference Types](#Scope-Definition-for-Reference-Types)), and `<builders>` is a file with the builders that `BEAPI` must use in generation (see section [3. (Optional) Run automated builders identification](#3.-(Optional)-Run-automated-builders-identification)).

**Note**: This script runs `BEAPI` with all optimizations enabled, that is, the `DEFAULT` configuration described in [BEAPI_OPT.md](BEAPI_OPT.md)).

Finally, to perform bounded exhaustive test generation in this example run:

```
./run-beapi.sh 5_github com.anthonynsimon.datastructures.MultiStackArray literals/literals3.txt properties/scope3.all.canonicalizer.properties config/5_github/builders/com.anthonynsimon.datastructures.MultiStackArray
```

The test suite generated by `BEAPI` is stored in folder `$BE_EXP_SRC/5_github/beapi-tests`.

### 4.1 Generate objects using `BEAPI` 

We can also use `BEAPI` to generate a bounded exhaustive set of objects for our case study, using the following script: 

```
./run-beapi-serialize.sh <folder> <case study> <literals> <configuration> <builders>
```
For example:

```
./run-beapi-serialize.sh 5_github com.anthonynsimon.datastructures.MultiStackArray literals/literals3.txt properties/scope3.all.canonicalizer.properties config/5_github/builders/com.anthonynsimon.datastructures.MultiStackArray
```

The objects are stored in file `$BE_EXP_SRC/5_github/beapi-tests/objects.ser`.

**Note**: For `BEAPI` to be able to serialize objects the class must implement `java.io.Serializable`.

