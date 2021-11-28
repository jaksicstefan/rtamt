import sys
import csv
import rtamt
import os

from syma.automaton.automaton import Location, SymbolicAutomaton
from syma.constraint.constraint import Constraint
from syma.constraint.node.node import *

from syma_arv.monitor.boolean import BooleanMonitor
from syma_arv.monitor.minmax import MinMaxMonitor
from syma_arv.monitor.tropical import TropicalMonitor

from rtamt.spec.stl.discrete_time.specification import Semantics


# take a spec, parse it and build a product automaton. then, do everything the same as in the main.py of the RV

def read_csv(filename):
    f = open(filename, 'r')
    reader = csv.reader(f)
    headers = next(reader, None)

    column = {}
    for h in headers:
        column[h] = []

    for row in reader:
        for h, v in zip(headers, row):
            column[h].append((float(row[0]), float(v)))

    return column


# ------------------------------------
if __name__ == "__main__":

    # this part to be replaced

    # Load traces
    # taken from offline discrete monitor
    data1 = read_csv('./examples/features/automata_based/example1.csv')
    # data2 = read_csv('example2.csv')
    # data3 = read_csv('example3.csv')
    # data4 = read_csv('example4.csv')

    # # #
    #
    # Example (a) - standard robustness
    #
    # # #
    spec = rtamt.STLDiscreteTimeSpecification(1)
    spec.name = 'Example 1'
    spec.declare_var('req', 'bool')
    spec.declare_var('gnt', 'bool')
    spec.declare_var('out', 'bool')
    spec.set_var_io_type('req', 'input')
    spec.set_var_io_type('gnt', 'output')
    #spec.spec = 'out = ((req>=3) implies (eventually[0:5](gnt>=3)))'
    #TODO - need to try one real-valued spec i.e. X>3 since p<2
    spec.spec = 'out = ( req  implies gnt )'
    spec.semantics = Semantics.STANDARD
    try:
        spec.parse()
        # spec.pastify() #WE DO NOT NEED TO PASTIFY THE ARV AUTOMATON, RIGHT?
    except rtamt.STLParseException as err:
        print('STL Parse Exception: {}'.format(err))
        sys.exit()

    print("FORMULA")
    print(spec.spec)
    print('\nSTART BUILDING THE AUTOMATON\n')

    my_automaton = spec.to_symbolic_automaton()  # this will be implemented as a visitor

    print("BUILDING AUTOMATA COMPLETED:")
    print(my_automaton)
    # for i in range(len(data1[' gnt'])):
    #    #rob = spec.update(i, [('req', data1[' req'][i][1]), ('gnt', data1[' gnt'][i][1])])
    #    rob = my_automaton.run(i, [('req', data1[' req'][i][1]), ('gnt', data1[' gnt'][i][1])])

    # print('Example (a) - standard robustness: {}'.format(rob))

    # above this to be replaced
    # print('Tropical:\n')
    # t_mon = TropicalMonitor(my_automaton)
    # t_mon.initialize()
    # print(str(t_mon.state))
    # t_mon.update({'a': 1})
    # print(str(t_mon.state))
    # t_mon.update({'a': 2})
    # print(str(t_mon.state))
    # t_mon.update({'a': 7})
    # print(str(t_mon.state))

    # print('MinMax:\n')
    # m_mon = MinMaxMonitor(my_automaton)
    # m_mon.initialize()
    # print(str(m_mon.state))
    # m_mon.update({'a': 1})
    # print(str(m_mon.state))
    # m_mon.update({'a': 2})
    # print(str(m_mon.state))
    # m_mon.update({'a': 7})
    # print(str(m_mon.state))

    # print('Boolean:\n')
    # b_mon = BooleanMonitor(my_automaton)
    # b_mon.initialize()
    # print(str(b_mon.state))
    # b_mon.update({'a': 1})
    # print(str(b_mon.state))
    # b_mon.update({'a': 2})
    # print(str(b_mon.state))
    # b_mon.update({'a': 7})
    # print(str(b_mon.state))
