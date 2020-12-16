from rtamt.node.stl.unary_node import UnaryNode

class Always(UnaryNode):
    """A class for storing STL Always nodes
        Inherits TemporalNode
    """

    def __init__(self, child, is_pure_python=True):
        """Constructor for Always

        Parameters:
            child : stl.Node
            bound : Interval
        """
        super(Always, self).__init__(child)

        self.in_vars = child.in_vars
        self.out_vars = child.out_vars

        self.name = 'always(' + child.name + ')'


        if is_pure_python:
            name = 'rtamt.operation.stl.always_operation'
            mod = __import__(name, fromlist=[''])
            self.node = mod.AlwaysOperation()
        else:
            name = 'rtamt.lib.rtamt_stl_library_wrapper.stl_node'
            mod = __import__(name, fromlist=[''])

            name = 'rtamt.lib.rtamt_stl_library_wrapper.stl_always_node'
            mod = __import__(name, fromlist=[''])
            self.node = mod.StlAlwaysNode()




