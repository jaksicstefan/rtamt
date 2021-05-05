import sys

from rtamt.ast.nodes.unary_node import UnaryNode


class Always(UnaryNode):
    """A class for storing STL Always nodes
        Inherits TemporalNode
    """

    def __init__(self, child):
        """Constructor for Always

        Parameters:
            child : stl.Node
            bound : Interval
        """
        if sys.version_info.major == 2:
            #super(UnaryNode, self).__init__(child)    #python2
            UnaryNode.__init__(self, child)
        else:
            super().__init__(child)    #python3

        self.in_vars = child.in_vars
        self.out_vars = child.out_vars

        self.name = 'always(' + child.name + ')'






