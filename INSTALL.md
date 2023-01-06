# Software Requirements

- Java 1.8
- Ant
- [Infer](https://fbinfer.com/)

# Installation

- Unzip the repository from zenodo
```
unzip beapi-artifact.zip 
```

- Move to the folder that containts the local copy of the repository, and set environment variable BE_EXP_SRC to this folder:
```
cd bounded-exhaustive-api-testgen
export BE_EXP_SRC=$(pwd)
```

## Installing dependencies

```
cd dependencies

sudo dpkg -i openjdk-8-jre-headless_8u352-ga-1~22.04_amd64.deb
sudo dpkg -i openjdk-8-jre_8u352-ga-1~22.04_amd64.deb
sudo dpkg -i openjdk-8-jdk-headless_8u352-ga-1~22.04_amd64.deb
sudo dpkg -i openjdk-8-jdk_8u352-ga-1~22.04_amd64.deb

sudo dpkg -i ant_1.10.12-1_all.deb 

sudo tar -C /opt -xf infer.tar.xz 
sudo ln -sf "/opt/infer-linux64-v1.0.0/bin/infer" /usr/local/bin/infer
sudo chown $USER:$USER $BE_EXP_SRC

```

Note: To configure `java 8` in your system you can run `sudo update-alternatives --config javac` and choose  option 3 (`/usr/lib/jvm/java-8-openjdk-amd64/bin/javac`),  then run  
`sudo update-alternatives --config java` and choose, one more time, option 3 (`/usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java`).

