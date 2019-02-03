#!/bin/bash

results=~/Documentos/Compiladores/c_tiger/tests/goodResults.txt
rm $results
touch $results

for filename in ~/Documentos/Compiladores/c_tiger/tests/good/*.tig; do
    ~/Documentos/Compiladores/c_tiger/entrega1/tiger -arbol "$filename" >> "$results"
done
