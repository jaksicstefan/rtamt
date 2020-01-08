# -*- coding: utf-8 -*-
"""
Created on Sun Jul 21 22:24:09 2019

@author: NickovicD
"""
from rtamt.node.stl.temporal_node import TemporalNode
from rtamt.lib.rtamt_stl_library_wrapper.stl_node import StlNode
from rtamt.lib.rtamt_stl_library_wrapper.stl_since_node import StlSinceNode
from rtamt.lib.rtamt_stl_library_wrapper.stl_since_bounded_node import StlSinceBoundedNode
from rtamt.operation.stl.since_operation import SinceOperation
from rtamt.operation.stl.since_bounded_operation import SinceBoundedOperation

class Since(TemporalNode):
    """A class for storing STL Since nodes
                Inherits TemporalNode
    """
    def __init__(self, child1, child2, bound, is_pure_python):
        """Constructor for Since node

            Parameters:
                child1 : stl.Node
                child2 : stl.Node
                bound : Interval
        """

        super(Since, self).__init__(bound)
        self.addChild(child1)
        self.addChild(child2)

        if is_pure_python:
            if bound == None:
                self.node = SinceOperation()
            else:
                self.node = SinceBoundedOperation(bound.begin, bound.end)
        else:
            if bound == None:
                self.node = StlSinceNode()
            else:
                self.node = StlSinceBoundedNode(bound.begin, bound.end)
