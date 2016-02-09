CXXFLAGS=-std=c++11 -Wall -g

all: seven_trees.vo

seven_trees.vo seven_search.v: seven_trees.v seven_search
	./seven_search > seven_search.v
	coqc seven_trees.v

.PHONY: all
