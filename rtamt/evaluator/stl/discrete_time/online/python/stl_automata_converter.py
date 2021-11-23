from rtamt.spec.stl.discrete_time.visitor import STLVisitor
from rtamt.exception.stl.exception import STLNotImplementedException
from rtamt.exception.ltl.exception import LTLNotImplementedException

from syma.automaton.automaton import Location, SymbolicAutomaton
from syma.constraint.constraint import Constraint, RealConstraint
from syma.constraint.node.node import  *

from z3 import *
from syma.constraint.translator.smt_translator import Constraint2SMT, RealConstraint2SMT, BoolConstraint2SMT
from rtamt.spec.stl.discrete_time.tt_builder import STL_TT_Builder

import inspect

# # #
# This visitor class will serve to convert an STL specification
# into an automaton, via conversion using temporal testers.
# We will not hash automata to adopt reuse of subformulas, because
# this would complicate the code and would bring very few benefits.
# # #
class STLAutomataConverter(STLVisitor):

    def __init__(self):
        self.node_automata_dict = dict()
        self.specification = None
        self.ttbuilder = STL_TT_Builder()

#    def generate(self, node):
#        self.visit(node, [])
#        return self.node_monitor_dict

#template:
#if top_level_tester -> multiply with always true
#create a tester
#visit kids.

    ###
    # top-level function of the class
    # converts STLDiscreteSpecification to syma automaton
    #
    ###
    def convert(self, specification):
        top_tester = self.visit(specification.top, None)
        #top_automaton = tester2automaton(top_tester)
        return top_tester

    ###
    # Sync and compose takes two temporal testers to create
    # a product temporal tester. The output of TT1 is
    # synchronized with TT2 input.
    # Assuming TT1 and TT2 are well formed.
    ###
    def syncAndCompose(self, tt1, tt2):
        compositionTT = SymbolicAutomaton()

        #track comp state names

        #add location and transitions
        for init_stateTT1 in tt1.init_locations:
            for init_stateTT2 in tt2.init_locations:
                #get all transitions for stateTT1 as a source
                #create and add all the initial states
                new_loc = Location(init_stateTT1.id+"_"+init_stateTT2.id, True, init_stateTT1.final and init_stateTT2.final)
                compositionTT.add_location(new_loc)
                comp_state_queue.append(new_loc)

        # while there are states to process, test all outgoing transitions
        # possible new states pushed to comp_state_queue
        while len(comp_state_queue) > 0:
            current_comp_state = comp_state_queue.pop()
            tt1stateid = int(current_comp_state.id.split('_'))[0]
            tt2stateid = int(current_comp_state.id.split('_'))[1]
            transitionsTT1 = tt1.outgoing[tt1stateid]
            transitionsTT2 = tt2.outgoing[tt2stateid]

            for t1 in transitionsTT1:
                for t2 in transitionsTT2:
                    comp_constraint = compose_constraints(t1.constraint, t2.constraint)

                    if comp_constraint.is_sat():
                        comp_constraint = compose_constraints(t1.constraint, t2.constraint)
                        sync_var = find_sync_var(tt1.alphabet.output_vars, tt2.alphabet.input_vars)
                        if (len(sync_var)>1) :
                            print("error! found more than one sync variable")

                        set_true(comp_constraint, sync_var)
                        new_state_id = t1.target.id+"_"+t2.target.id

                        if not(new_state_id in compositionTT.locations[id]):
                            new_loc = Location(new_state_id, t1.target.initial and t2.target.initial,
                                               init_stateTT1.final and init_stateTT2.final)
                            compositionTT.add_location(new_loc) #add new state
                            comp_state_queue.append(new_loc)    #and process it later on

                        compositionTT.add_transition(current_comp_state, new_state_id, comp_constraint)
                    else :
                        continue
        return compositionTT

    #####
    # produces cstr1 AND cstr2
    ###
    def compose_constraints(self, cstr1, cstr2):
        and_node = AndNode(cstr1, cstr2)
        return RealConstraint(formula=and_node)

    #TODO - has to point to new ALPHABET (LOCAL)
    def find_sync_var(self, alphabet1, alphabet2):
        sync_var = alphabet1.output_vars.intersection(alphabet2.input_vars)
        if len(sync_var) == 0:
            print("ERROR: Sync var not found! Cannot proceed with the product.")
        return sync_var

    ###
    # sets the common variable to true
    # works for a variable and the negated variable
    # recursively traverses the formula
    # assumptions: there is only one common_var
    #              it is invoked only after cst.is_sat() = true
    ###
    def set_true(self, cstr1, common_var):

        if (self.formula == common_var):
            self.formula = ConstantNode(True and (not not_node))

        if isinstance(cstr1, NotNode):  #handleInvertedVars
            not_node = true
        else :
            not_node = false

        for child in cstr1.children :
            set_true(child, common_var)

########## visitor functions ####################

    def visitPredicate(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name+" "+node.name)

        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)

        #TODO - to remove!
        return SymbolicAutomaton


    def visitVariable(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name+" "+node.name)

        inVar0 = node.name
        print("NODE NAME"+node.name)

        ttester = self.ttbuilder.getVariableTester( inVar0, [0,1])
        return ttester


    def visitAbs(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)

        in_sample = self.visit(node.children[0], args)

    def visitSqrt(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)

        in_sample = self.visit(node.children[0], args)


    def visitExp(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)

        in_sample = self.visit(node.children[0], args)


    def visitPow(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)


    def visitAddition(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)


    def visitSubtraction(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)


    def visitMultiplication(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)

    def visitDivision(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitNot(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)


    def visitAnd(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitOr(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitImplies(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)

        tt_child_1: SymbolicAutomaton = self.visit(node.children[0], args)
        tt_child_2: SymbolicAutomaton = self.visit(node.children[1], args)

        inVar0 = tt_child_1.alphabet.output_vars[0]
        inVar1 = tt_child_2.alphabet.output_vars[0]

        ttImplies = self.ttbuilder.getImpliesTester( inVar0, [0,1], inVar1, [0,1])

        tt_composition = syncAndCompose(tt_child_1, ttImplies)
        tt_composition = syncAndCompose(tt_child_2, tt_composition)
        return tt_composition





    def visitIff(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitXor(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)


    def visitEventually(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)



    def visitAlways(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)



    def visitUntil(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitOnce(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)


    def visitHistorically(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)


    def visitSince(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitRise(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)


    def visitFall(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)


    def visitConstant(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name+" "+node.name)

        #TODO - to remove!
        return SymbolicAutomaton



    def visitPrevious(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)


    def visitNext(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)

        raise LTLNotImplementedException('Next operator not implemented in STL online monitor.')


    def visitTimedPrecedes(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitTimedOnce(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)


    def visitTimedHistorically(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)



    def visitTimedSince(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)



    def visitTimedAlways(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)

        raise STLNotImplementedException('Bounded always operator not implemented in STL online monitor.')


    def visitTimedEventually(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample = self.visit(node.children[0], args)

        #TODO - to remove!
        return SymbolicAutomaton


    def visitTimedUntil(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)

        raise STLNotImplementedException('Bounded until operator not implemented in STL online monitor.')


    def visitDefault(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name)
        pass