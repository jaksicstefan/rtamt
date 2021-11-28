# # #
# this class is a service class to build basic temporal testers
# for each STL operator in dicrete time
# # #
import syma
from numpy import outer
from syma.automaton.automaton import Location, SymbolicAutomaton
from syma.constraint.constraint import Constraint, BoolConstraint ,RealConstraint
from syma.constraint.node.node import *


class STL_TT_Builder():
    var_naming_cnt = 0

    def getNewVar(self):
        self.var_naming_cnt += 1
        return "z" + str(self.var_naming_cnt)

    def getImpliesTester(self, inVar0, dom0, inVar1, dom1, outVar=None):
        # resetIDs
        ttester = SymbolicAutomaton()
        myOutVar = outVar

        # add i/o vars
        ttester.add_var(inVar0, dom0, "IN")
        ttester.add_var(inVar1, dom1, "IN")

        if myOutVar is None:
            myOutVar = self.getNewVar()
            ttester.add_var(myOutVar, [0, 1], "OUT")  # Boolean
        else:
            ttester.add_var(myOutVar, [0, 1], "OUT")  # Boolean

        loc0 = Location(0, initial=True, final=True)

        cst0 = AndNode(NotNode(VariableNode(inVar0)), NotNode(VariableNode(inVar1)))
        cst1 = AndNode(NotNode(VariableNode(inVar0)),        (VariableNode(inVar1)))
        cst2 = AndNode(        VariableNode(inVar0),  NotNode(VariableNode(inVar1)))
        cst3 = AndNode(        VariableNode(inVar0),         (VariableNode(inVar1)))

        cst_out = VariableNode(myOutVar)
        cst_out_neg = NotNode(VariableNode(myOutVar))

        ttester.add_location(loc0) #init, acc

        #TODO?bool or real constraint?
        ttester.add_transition(loc0, loc0, BoolConstraint(formula=AndNode(cst0, cst_out)))
        ttester.add_transition(loc0, loc0, BoolConstraint(formula=AndNode(cst1, cst_out)))
        ttester.add_transition(loc0, loc0, BoolConstraint(formula=AndNode(cst2, cst_out_neg)))
        ttester.add_transition(loc0, loc0, BoolConstraint(formula=AndNode(cst3, cst_out)))

        return ttester


    def getVariableTester(self, inVar0, dom0, outVar=None):
        # resetIDs
        ttester = SymbolicAutomaton()
        myOutVar = outVar

        # add i/o vars
        ttester.add_var(inVar0, dom0, "IN")
        #aut.add_var('a', [-10, 10])
        if myOutVar is None:
            myOutVar = self.getNewVar()
            ttester.add_var(myOutVar, [0, 1], "OUT")  # Boolean
        else:
            ttester.add_var(myOutVar, [0, 1], "OUT")  # Boolean

        loc0 = Location(0, initial=True, final=True)

        cst0 = NotNode(VariableNode(inVar0))
        cst1 = VariableNode(inVar0)

        cst_out = VariableNode(myOutVar)
        cst_out_neg = NotNode(VariableNode(myOutVar))

        ttester.add_location(loc0) #init, acc

        ttester.add_transition(loc0, loc0, BoolConstraint(formula=AndNode(cst0, cst_out_neg)))
        ttester.add_transition(loc0, loc0, BoolConstraint(formula=AndNode(cst1, cst_out)))
        return ttester

