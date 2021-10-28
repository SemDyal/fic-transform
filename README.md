# Flow-Insensitive-Complete program transformation
for VMCAI 22

Setup the opam environnement
```
opam switch create fic 4.13.1
opam install sawja
eval $(opam env)
```

Downloading external benchmark
```
curl --output apache-ivy-2.5.0-bin.zip https://dlcdn.apache.org//ant/ivy/2.5.0/apache-ivy-2.5.0-bin.zip
unzip apache-ivy-2.5.0-bin.zip
```

Compile and launch tests
```
make
make test
```