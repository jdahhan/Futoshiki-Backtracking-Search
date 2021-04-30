"""
Johnlouis Dahhan
CS 4613 Spring 2021
AI Project 2: Futoshiki puzzle
Implements a possible solution for the Futoshiki puzzle using Backtracking CSP search
Uses forward checking and unassigned variables are selected with MRV and degree heuristics
Reads puzzle from input file and writes to output file
"""
from copy import deepcopy  # need this too create new branches

# CHANGE INFILE/OUTFILE TO RUN
INFILE = "Input1.txt"
OUTFILE = "Output1.txt"

# Global variables
SIDE = 6
HGT = '>'
HLT = '<'
VGT = 'v'
VLT = '^'
Y_IND = 0
X_IND = 1


class Node:
    def __init__(self, value):
        """
        creates a node with a value, domain and constraint lists
        if value is given the domain is restricted to that value
        :param value: value of node
        """
        self.value = value  # value of node, if 0 assume that it is unassigned
        if self.value > 0:
            self.domain = [self.value]  # restrict domain to value if not assigned
        else:
            self.domain = [i for i in range(1, SIDE + 1)]  # initialize domain to all possible values
        self.gt = []  # list of nodes that self is greater than
        self.lt = []  # list of nodes that self is less than

    def set_val(self, val):
        """
        easy function to set a value and wipe domain
        :param val: value to set
        :return: 
        """
        self.value = val
        self.domain = [val]

    def remove_val(self, val):
        """
        removes a value from domain, returns whether or not there is an inconsistency after
        :param val: value to be removed
        :return boolean: False if inconsistent, else True
        """
        consistent = True
        if val in self.domain:
            self.domain.remove(val)
            consistent = len(self.domain) != 0  # only consistent if domain not empty
            if len(self.domain) == 1:
                self.set_val(self.domain[0])  # set the value if it's the last one left
        return consistent

    def forward_check(self):
        """
        performs a round of forward checking on a node's adjacency constraints
        :return boolean, True if consistent, False if not
        """
        # CHECK GREATER THAN
        for other in self.gt:
            for val in self.domain:
                if not any(val > other_val for other_val in other.domain):
                    consistent = self.remove_val(val)  # remove value from domain if it cannot fill constraint
                    if not consistent:  # return False if self.domain is empty
                        return False
            for other_val in other.domain:
                if not any(other_val < val for val in self.domain):
                    consistent = other.remove_val(other_val)
                    if not consistent:  # return False if other.domain is empty
                        return False
        # CHECK LESS THAN
        for other in self.lt:
            for val in self.domain:
                if not any(val < other_val for other_val in other.domain):
                    consistent = self.remove_val(val)  # remove value from domain if it cannot fill constraint
                    if not consistent:  # return False if self.domain is empty
                        return False
            for other_val in other.domain:
                if not any(other_val > val for val in self.domain):
                    consistent = other.remove_val(other_val)
                    if not consistent:  # return False if other.domain is empty
                        return False
        return True  # if we've made it this far, we have maintained consistency (so far)


def read_board(filepath):
    """
    creates a board from an input file
    :param filepath: name of input file
    :return: board populated with nodes
    """
    file = open(filepath, 'r')
    board = [[] for _ in range(SIDE)]
    # READ VALUES
    for i in range(SIDE):
        curr_line = file.readline().strip().split()  # read line as a list
        board[i] = [Node(int(val)) for val in curr_line]  # move values to board
    # READ HORIZONTAL CONSTRAINTS
    file.readline()
    for y in range(SIDE):  # check for and add constraints
        curr_line = file.readline().strip().split()
        for x in range(SIDE - 1):  # fewer columns, constraint points to the one on its right
            if curr_line[x] == HGT:
                board[y][x].gt.append(board[y][x + 1])
                board[y][x + 1].lt.append(board[y][x])
            if curr_line[x] == HLT:
                board[y][x].lt.append(board[y][x + 1])
                board[y][x + 1].gt.append(board[y][x])
    # READ VERTICAL CONSTRAINTS
    file.readline()
    for y in range(SIDE - 1):  # fewer rows, each constraint points to the node below it
        curr_line = file.readline().strip().split()
        for x in range(SIDE):  # check for an add constraint
            if curr_line[x] == VGT:
                board[y][x].gt.append(board[y + 1][x])
                board[y + 1][x].lt.append(board[y][x])
            if curr_line[x] == VLT:
                board[y][x].lt.append(board[y + 1][x])
                board[y + 1][x].gt.append(board[y][x])
    file.close()
    # FORWARD CHECK ALL NODES IN ADVANCE
    for y in range(SIDE):
        for x in range(SIDE):
            forward_check(board, (y, x))
    return board


def select_unassigned(board):
    """
    selects the best node to check for backtracking search
    the heuristics used are the MRV and degree heuristics
    :param board: 2d list of nodes
    :return position: tuple position of a good node to start with
    """
    remaining = []
    mrv = SIDE
    # look for the smallest remaining domains for unassigned values
    for y in range(len(board)):  # find smallest domain size
        for x in range(len(board[y])):
            if 1 < len(board[y][x].domain) < mrv:
                mrv = len(board[y][x].domain)
    for y in range(len(board)):  # only consider smallest domain nodes
        for x in range(len(board[y])):
            if len(board[y][x].domain) == mrv:
                remaining.append((y, x))
    # check for largest number of constraints
    degree = 0
    for y, x in remaining:  # find max degree
        curr_deg = len(board[y][x].lt) + len(board[y][x].gt)
        if curr_deg > degree:
            degree = curr_deg
    for y, x in remaining:  # isolate nodes with max degree
        curr_deg = len(board[y][x].lt) + len(board[y][x].gt)
        if curr_deg != degree:
            remaining.remove((y, x))
    # return the first node remaining, doesn't matter if any other are left
    return remaining[0]


def forward_check(board, pos):
    """
    supplements forward checking with row/column equivalence checking
    didn't want to bloat node class
    :param board: 2d list of nodes representing board
    :param pos: position of current node
    :return:
    """
    y, x = pos
    val = board[y][x].value
    if board[y][x].forward_check():
        if val > 0:
            # CHECK COLUMN
            for i in range(SIDE):
                if i != y:  # don't want to remove the value from the current node!
                    if not board[i][x].remove_val(val):
                        return False
            # CHECK ROW
            for i in range(SIDE):
                if i != x:  # don't want to remove the value from the current node!
                    if not board[y][i].remove_val(val):
                        return False
        return True
    else:
        return False


def complete(board):
    """
    returns if board all nodes have values
    :param board:
    :return: boolean, if board is complete
    """
    for row in board:
        for node in row:
            if not node.value:  # if the value is still 0, node can still be specified
                return False
    return True


def backtrack(board):
    """
    performs one step of backtracking search
    :param board: current board
    :return new_board: deepcopy of board at next step
    """
    if complete(board):
        print("COMPLETE")
        return board
    y, x = select_unassigned(board)
    for val in board[y][x].domain:
        new_board = deepcopy(board)
        curr_var = new_board[y][x]
        curr_var.set_val(val)
        if forward_check(new_board, (y, x)):
            final = backtrack(new_board)
            if final:  # if this result isn't empty, this branch has a solution we can return
                return final
    return []  # if we try all the domain values and none work, we backtrack


def backtracking_search(infile, outfile):
    """
    conducts backtracking search, outputs a solved board to outfile
    :param infile: input filepath
    :param outfile: output filepath
    """
    board = read_board(infile)
    final_board = backtrack(board)
    output_board = []
    for row in final_board:
        output_board.append(" ".join([str(node.value) for node in row]) + '\n')
    file = open(outfile, 'w')
    file.writelines(output_board)
    file.close()


if __name__ == '__main__':
    backtracking_search(INFILE, OUTFILE)
