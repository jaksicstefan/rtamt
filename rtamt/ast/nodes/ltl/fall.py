import sys

from rtamt.ast.nodes.unary_node import UnaryNode


class Fall(UnaryNode):
    """A class for storing STL Neg nodes
        Inherits Node
    """
    def __init__(self, child):
        """Constructor for Neg node

            Parameters:
                child : stl.Node
        """
        name_phrase = 'fall'
        if sys.version_info.major == 2:
            super(Fall, self).__init__(name_phrase, child)    #python2
        else:
            super().__init__(name_phrase, child)    #python3
