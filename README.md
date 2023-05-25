# TLA+ specifications

A collection of TLA+ specifications.

```sh
# check model
./run.sh vmachine/VendingMachine

# simulate random behavior
export TLC_OPTS="-simulate -workers 1 -metadir /tmp/tlc file=/tmp/tlc/simulation.txt,num=1 -depth 10"
./run.sh vmachine/VendingMachine

# generate state graph (small models only)
export TLC_OPTS="-modelcheck -workers auto -metadir /tmp/tlc -noGenerateSpecTE -dump dot,colorize,actionlabels /tmp/tlc/graph.dot"
./run.sh vmachine/VendingMachine
dot -Tpng /tmp/tlc/graph.dot > state-graph.png
```
