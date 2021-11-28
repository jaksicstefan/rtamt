from rtamt.spec.stl.discrete_time.visitor import STLVisitor
from rtamt.exception.stl.exception import STLNotImplementedException
from rtamt.exception.ltl.exception import LTLNotImplementedException

from syma.automaton.automaton import Location, SymbolicAutomaton
from syma.alphabet.aphabet import Alphabet
from syma.constraint.constraint import Constraint, BoolConstraint, RealConstraint
from syma.constraint.node.node import *

from z3 import *
from syma.constraint.translator.smt_translator import Constraint2SMT, RealConstraint2SMT, BoolConstraint2SMT
from rtamt.spec.stl.discrete_time.tt_builder import STL_TT_Builder
from copy import  deepcopy


import inspect


# # #
# This visitor class will serve to convert an STL specification
# into an automaton, via conversion using temporal testers.
# We will not hash automata to adopt reuse of subformulas, because
# this would complicate the code and would bring very few benefits.
# # #

class LocationPair:
    def __init__(self, location1, location2):
        self.loc1 = location1
        self.loc2 = location2


class STLAutomataConverter(STLVisitor):

    def __init__(self):
        self.node_automata_dict = dict()
        self.specification = None
        self.ttbuilder = STL_TT_Builder()
        self.action = 0

    #    def generate(self, node):
    #        self.visit(node, [])
    #        return self.node_monitor_dict

    # template:
    # if top_level_tester -> multiply with always true
    # create a tester
    # visit kids.

    ###
    # top-level function of the class
    # converts STLDiscreteSpecification to syma automaton
    #
    ###
    def convert(self, specification):
        top_tester = self.visit(specification.top, None)
        # top_automaton = tester2automaton(top_tester)
        return top_tester

    ###
    # Sync and compose takes two temporal testers to create
    # a product temporal tester. The output of TT1 is
    # synchronized with TT2 input.
    # Assuming TT1 and TT2 are well formed.
    ###
    def syncAndCompose(self, tt1, tt2):
        print("syncAndCompose")

        compositionTT = SymbolicAutomaton()

        sync_var = self.find_sync_var(tt1.alphabet.output_vars, tt2.alphabet.input_vars)

        for var1 in tt1.alphabet.vars:
            if (var1 != sync_var):
                compositionTT.add_var(var1, tt1.alphabet.vars_domain[var1], tt1.alphabet.vars_iodomain[var1])

        for var2 in tt2.alphabet.vars:
            if (var2 != sync_var):
                compositionTT.add_var(var2, tt2.alphabet.vars_domain[var2], tt2.alphabet.vars_iodomain[var2])

        state_origin = dict()

        # track comp state names
        comp_state_queue = []
        # add location and transitions
        for init_stateTT1 in tt1.init_locations:
            for init_stateTT2 in tt2.init_locations:
                # get all transitions for stateTT1 as a source
                # create and add all the initial states
                newid = str(init_stateTT1.id) + str(init_stateTT2.id)
                new_loc = Location(newid, True, init_stateTT1.final and init_stateTT2.final)
                state_origin[newid] = LocationPair(init_stateTT1, init_stateTT2)
                compositionTT.add_location(new_loc)
                comp_state_queue.append(new_loc)

        # while there are states to process, test all outgoing transitions
        # possible new states pushed to comp_state_queue
        while len(comp_state_queue) > 0:
            current_comp_state = comp_state_queue.pop()
            original_states = state_origin[current_comp_state.id]

            transitionsTT1 = tt1.outgoing[original_states.loc1.id]
            transitionsTT2 = tt2.outgoing[original_states.loc2.id]

            for trans1 in transitionsTT1:
                for trans2 in transitionsTT2:

                    t1 = [trans1[0], trans1[1], trans1[2], copy.deepcopy(trans1[3])]
                    t2 = [trans2[0], trans2[1], trans2[2], copy.deepcopy(trans2[3])]

                    print("checking tt1: " + str(t1[0])+ " and tt2: "+ str(t2[0]))
                    comp_constraint = self.compose_constraints(t1[3], t2[3])

                    if comp_constraint.is_sat():

                        print("SYNC VAR"+str(sync_var))
                        print("BEFORE " + str(comp_constraint.formula))
                        self.remove_sync_var(comp_constraint.formula, sync_var)

                        mu_var_br = 0

                        print("AFTER "+str(comp_constraint.formula))
                        new_state_id = str(t1[2].id) + str(t2[2].id)  # [2] is target

                        locidset = set()

                        for loc in compositionTT.locations:  # get all location ids
                            locidset.add(loc.id)

                        if not (new_state_id in locidset):
                            dst_loc = Location(new_state_id, t1[2].initial and t2[2].initial,
                                               t1[2].final and t2[2].final)

                            state_origin[new_state_id] = LocationPair(t1[2], t2[2])
                            compositionTT.add_location(dst_loc)  # add new state
                            comp_state_queue.append(dst_loc)  # and process it later on
                        else:  # location already exists
                            for locx in compositionTT.locations:
                                if locx.id == new_state_id:
                                    break
                            dst_loc = locx

                        #print("compositionTT adding transition")
                        compositionTT.add_transition(current_comp_state, dst_loc, comp_constraint)
                        #print("compositionTT ADDED transition")

        return compositionTT

    #####
    # produces cstr1 AND cstr2
    ###
    def compose_constraints(self, cstr1, cstr2):
        and_node = AndNode(cstr1.formula, cstr2.formula)
        cstr = BoolConstraint(formula=and_node)
        return cstr

    def find_sync_var(self, output_vars, input_vars):
        sync_var = output_vars.intersection(input_vars)
        if len(sync_var) == 0:
            print("ERROR: Sync var not found! Cannot proceed with the product.")
        if len(sync_var) > 1:
            print("ERROR: More than one sync var found.")

        return sync_var.pop()

    ###
    # sets the common variable to true
    # works for a variable and the negated variable
    # recursively traverses the formula
    # assumptions: there is only one common_var
    #              it is invoked only after cst.is_sat() = true
    ###
    def set_true(self, formula, common_var, not_node=False):

        if (isinstance(formula, VariableNode) and (formula.name == common_var)):
            if not_node:
                formula = ConstantNode(False)
            else:
                formula = ConstantNode(True)

        if isinstance(formula, NotNode):  # handleInvertedVars
            not_node = True
        else:
            not_node = False

        new_children = []
        for child in formula.children:
            new_children.append(self.set_true(child, common_var, not_node))

        formula.children = new_children
        return formula

    ###
    # start from top and reach the bottom
    # if found a sync var, propagate upward
    ####

    def remove_sync_var(self, formula, common_var):
        print("\tinput formula: " + str(formula))

        #print("common var"+ common_var)

        #if no chioldern
        if isinstance(formula, VariableNode) and (formula.name == common_var):
            print("FOUND")
            self.action = 1
        else:
            print("FOUND ___")
            self.action = self.action or 0

        for idx, child in enumerate(formula.children):

            self.remove_sync_var(child, common_var)

            print("returned action "+ str(self.action))

            if (self.action == 3): #connect grandfather and grandson
                #print("returned 3 from a node "+ str(child))
                print("bypassing the father")
                formula.children[idx] = child.children[0]
                self.action = 0
            elif (self.action == 2): #just in case of a unary operator Not
                print("2 child removed: " )
                formula.children.remove(child)
                self.action = 3
            elif (self.action == 1):
                #delete child and propagate 2 upward
                if isinstance(formula, NotNode):  # handleInvertedVars
                    print("1 child removed: " + str(child))
                    formula.children.remove(child)
                    self.action = 2
                else:
                    self.action = 3
            elif (self.action == 0): #? redundant case?
                if isinstance(formula, VariableNode) and (formula.name == common_var):
                    self.action = 1
                else:
                    print("FOUNDX") #? case NOT(non-sync-var)
                    self.action = self.action or 0
            else:
                #print("ERROR : illegal value during constraing update")
                print("error! the action is None")
        #return 0
        #return 0







    def old_remove_sync_var(self, formula, common_var):

        for idx, child in enumerate(formula.children):
            print("\tcontext" + str(child))

            to_remove = self.remove_sync_var(child, common_var)

            if isinstance(formula, VariableNode) and (formula.name == common_var):
                print("FOUND")
                return True

            print("to remove" + str(to_remove))

            if not (to_remove is False):  # sync var found in a child

                if isinstance(formula, NotNode):  # handleInvertedVars
                    print("2B")
                    return True
                else:
                    print("1A")
                    formula.children.remove(formula.children[idx])
                    formula = formula.children[0]
                    #self.prop_form = None

                    #print("3C")
                    # not_node = False  #replace here
                    #print("current_node " + str(formula))
                    #print("removing child " + str(child))
                    #print("replacing with " + str(formula.children[0]))
                    #print("ACTUALLY REMOVE"+ str(child) + " FROM " + str(formula))
                    #formula.children.remove(child)
                    #formula = formula.children[0]
                    #print("replaced with " + str(formula.children[0]))
                    #self.prop_form = formula.children[0] OVDE TREBA DRUGO DETE
                    return False


    ########## visitor functions ####################

    def visitPredicate(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name + " " + node.name)

        in_sample_1 = self.visit(node.children[0], args)
        in_sample_2 = self.visit(node.children[1], args)

        # TODO - to remove!
        return SymbolicAutomaton

    def visitVariable(self, node, args):
        func_name = inspect.stack()[0][3]
        print(func_name + " " + node.name)

        inVar0 = node.name
        # print("NODE NAME"+node.name)

        ttester = self.ttbuilder.getVariableTester(inVar0, [0, 1])
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

        print(tt_child_1)
        print(tt_child_2)

        inVar0 = next(iter(tt_child_1.alphabet.output_vars))
        inVar1 = next(iter(tt_child_2.alphabet.output_vars))

        ttImplies = self.ttbuilder.getImpliesTester(inVar0, [0, 1], inVar1, [0, 1])

        tt_composition = self.syncAndCompose(tt_child_1, ttImplies)
        somvear = 'XXX'
        tt_composition = self.syncAndCompose(tt_child_2, tt_composition)
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
        print(func_name + " " + node.name)

        # TODO - to remove!
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

        # TODO - to remove!
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
