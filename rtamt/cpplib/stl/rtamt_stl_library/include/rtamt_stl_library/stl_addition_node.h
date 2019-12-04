/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   stl_addition_node.h
 * Author: nickovic
 *
 * Created on December 4, 2019, 11:31 AM
 */

#ifndef STL_ADDITION_NODE_H
#define STL_ADDITION_NODE_H

#include <rtamt_stl_library/stl_sample.h>
#include <rtamt_stl_library/stl_node.h>

namespace stl_library {

class StlAdditionNode : public StlNode {
    private:
        Sample in[2];
        void addNewInput(int i, Sample msg);
        
        
    public:
        StlAdditionNode();
        Sample update();
        void addNewInput(Sample left, Sample right);      
};

} // namespace stl_library

#endif /* STL_ADDITION_NODE_H */

