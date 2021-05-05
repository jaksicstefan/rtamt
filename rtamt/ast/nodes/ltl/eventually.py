import sys

from rtamt.ast.nodes.unary_node import UnaryNode


class Eventually(UnaryNode):
    """A class for storing STL Eventually nodes
            Inherits TemporalNode
    """
    def __init__(self, child):
        """Constructor for Eventually node

        Parameters:
            child : stl.Node
            bound : Interval
        """
        if sys.version_info.major == 2:
            #super(UnaryNode, self).__init__(child)    #python2
            UnaryNode.__init__(self, child)
        else:
            super().__init__(child)    #python3

        self.name = 'eventually(' + child.name + ')'
