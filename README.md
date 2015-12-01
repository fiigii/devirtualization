# devirtualization
Devirtualization (convert dynamic dispatch to direct function call) optimization for a subset Scala (named COOL 2015).   
The `Analysis.scala` file includes two approaches to implement the devirtualization optimization, class hierarchy analysis and 0-CFA.

## Class Hierarchy Analysis
For CHA, following Chambers’ paper, there are two important data structures, cone set for each class and applies-to set for each method, which are implemented with Map. Firstly, the ClassHirerachyAnalysis object collect classes and methods information of whole program to compute these sets. Then when the analysis runs on a program, the `potentialMethods` computes all the potentially method for a concrete receiver’s static type and invoked method name, though the inherence graph (computed by `allSuperClasses` and `traverseOverride` method). If there is a method whose applies-to set does not overlap the cone set of receiver’s static type, this method may be called in runtime. Finally, if a receiver cannot be null (computed by `NonNullVisitor. notNull`) and just one method in overlap set, the method can be directly invoked.

## Context-insensitive Control Flow Analysis (0-CFA)
For 0-CFA, the ControlFlowAnalysis class has three significant properties, the type flow cache for every statement (setS) and expression (setE) that are represented by a Map that keys are AST nodes’ id and values are a set containing all the types flow into the node. Meanwhile, the arraySetObj filed always refers to the AST node of the second formal parameter of ArrayAny.set. Additionally, if a method’s id is n, there is a –n representing the sigma of the method, so for a method m with id n the setS(sigmaOf(m)) is setS(-n). InternalCFA class inherent form ControlFlowAnalysis class has a additional `outer` filed referring to the “current method” node to analyze static dispatch and variable (`this`) node, each method definition node creates a InternalCFA object to analyze its body. In the optimizer, if there is a receiver’s setE just containing one type, we can statically dispatch the method on this type.

## Effect of Optimizations
Devirtualization:
```
+================+=========+==========+
| Files/Analysis |   CHA   |  0-CFA   |
+================+=========+==========+
| gfx            | 57.732% | 75.401%  |
+----------------+---------+----------+
| resolve        | 69.167% | 72.807%  |
+----------------+---------+----------+
| semant         | 44.079% | Too Slow |
+----------------+---------+----------+
```


Dead Method Bodies Removing:
```
+================+========+
| Files/Analysis | 0-CFA  |
+================+========+
| gfx            | 3.922% |
+----------------+--------+
| resolve        | 2.597% |
+----------------+--------+
```

Dead Case Branches Removing:
```
+================+========+
| Files/Analysis | 0-CFA  |
+================+========+
| gfx            | 20.0%  |
+----------------+--------+
| resolve        | 45.0%  |
+----------------+--------+
```

## Author  
* Fei Peng

## Copyright

Copyright (c) 2015 Fei Peng