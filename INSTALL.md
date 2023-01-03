# Software Requirements

- Java 1.8
- Ant
- Infer

# Installation

- Clone the repository to your computer:
```
git clone https://github.com/mpolitano/bounded-exhaustive-api-testgen.git
```
CAMBIAR A ZENODO ZIP 

- Move to the folder that containts the local copy of the repository, and set environment variable BE_EXP_SRC to this folder:
```
cd bounded-exhaustive-api-testgen
export BE_EXP_SRC=$(pwd)
```

## Installing dependencies

```
cd dependencies
dpkg -i openjdk-8-jdk_8u352-ga-1~22.04_amd64.deb
dpkg -i ant_1.10.12-1_all.deb 
```
AGREGAR instrucciones de INFER


Note: To configurate `java 8` in your system you can run `sudo update-alternative --config javac` and choose `java 8` option,  then run  
`sudo update-alternative-alternatives --config java` and choose, one more time, `java 8` option.

