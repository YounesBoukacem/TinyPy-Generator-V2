from anytree import Node, RenderTree
import random
from io import StringIO
from contextlib import redirect_stdout
import argparse  
import time
from tqdm.auto import tqdm
import hashlib
import os
import psutil


class CodeGenerator:
    def __init__(self):
        """
        Initialize the CodeGenerator object with the given context-free grammar rules.

        """
        
        self.init_count = 0
        self.max_init = 0
        
        # Dictionary containing context-free grammar rules.
        self.cfg_rules = {
                # Variables and digits
                "VARIABLE": ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z" ],
                "DIGIT": [str(i) for i in range(256)],

                # Operators
                "ARITHMETIC_OPERATOR": ["+", "-", "*", "/"],
                "RELATIONAL_OPERATOR": ["<", ">", "<=", ">=", "!=", "=="],
                "LOGICAL_OPERATOR_INFIX": ["and", "or"],
                "LOGICAL_OPERATOR_PREFIX": ["not"],
                "LOGICAL_OPERATOR": ["LOGICAL_OPERATOR_INFIX", "LOGICAL_OPERATOR_PREFIX"],
                "OPERATOR": ["ARITHMETIC_OPERATOR"], 

                # Formatting
                "NEW_LINE": ["\n"],
                "TAB_INDENT": ["\t"],
                "BRACKET_OPEN": ['('],
                "BRACKET_CLOSE": [')'],
                "EQUALS": ["="],
                "COLON": [":"],
                "COMMA": [","],


                # Keywords
                "IF": ["if"],
                "ELIF": ["elif"],
                "ELSE": ["else"],
                "FOR": ["for"],
                "IN": ["in"],
                "RANGE": ["range"],
                "WHILE": ["while"],
                "PRINT": ["print"],

                # Terms and expressions
                "TERM": ["EXPRESSION_IDENTIFIER", "DIGIT"],
                "EXPRESSION": ["TERM SPACE OPERATOR SPACE TERM"],
                "ENCLOSED_EXPRESSION": ["BRACKET_OPEN EXPRESSION BRACKET_CLOSE"],
                "DISPLAY_EXPRESSION": ["EXPRESSION_IDENTIFIER SPACE OPERATOR SPACE EXPRESSION_IDENTIFIER" ,
                                        "EXPRESSION_IDENTIFIER SPACE OPERATOR SPACE DIGIT"],

                # Initializations and assignments
                "IDENTIFIER_INITIALIZATION": ["IDENTIFIER_INITIALIZATION INITIALIZATION", 
                                              "INITIALIZATION"],

                "INITIALIZATION": ["VARIABLE SPACE EQUALS SPACE DIGIT NEW_LINE"],

                "SIMPLE_ASSIGNMENTS": ["VARIABLE SPACE EQUALS SPACE EXPRESSION NEW_LINE" , ""],
                "ADVANCED_ASSIGNMENTS": ["VARIABLE SPACE EQUALS SPACE SIMPLE_ARITHMETIC_EVALUATION NEW_LINE", 
                                         "VARIABLE SPACE EQUALS SPACE EXPRESSION NEW_LINE" , 
                                         ""],

                "SIMPLE_ARITHMETIC_EVALUATION": ["SIMPLE_ARITHMETIC_EVALUATION ARITHMETIC_OPERATOR ENCLOSED_EXPRESSION", 
                                                 "ENCLOSED_EXPRESSION",
                                                ], 

                # Conditions
                "SIMPLE_IF_STATEMENT": ["IF SPACE CONDITION SPACE COLON NEW_LINE"],
                "ADVANCED_IF_STATEMENT": ["IF SPACE CHAIN_CONDITION SPACE COLON NEW_LINE"],
                "SIMPLE_ELIF_STATEMENT": ["ELIF SPACE CONDITION SPACE COLON NEW_LINE"],
                "ADVANCED_ELIF_STATEMENT": ["ELIF SPACE CHAIN_CONDITION SPACE COLON NEW_LINE"],
                "ELSE_STATEMENT": ["ELSE SPACE COLON NEW_LINE"],

                "CHAIN_CONDITION": ["CHAIN_CONDITION SPACE LOGICAL_OPERATOR_INFIX SPACE ENCLOSED_CONDITION", 
                                    "LOGICAL_OPERATOR_PREFIX SPACE ENCLOSED_CONDITION", 
                                    "ENCLOSED_CONDITION"],
                "ENCLOSED_CONDITION": ["BRACKET_OPEN CONDITION BRACKET_CLOSE"],
                "CONDITION": ["OPTIONAL_NOT CONDITION_EXPRESSION", "CONDITION_EXPRESSION"],
                "CONDITION_EXPRESSION": ["EXPRESSION_IDENTIFIER SPACE RELATIONAL_OPERATOR SPACE EXPRESSION_IDENTIFIER", 
                                         "EXPRESSION_IDENTIFIER SPACE RELATIONAL_OPERATOR SPACE DIGIT"],
                "OPTIONAL_NOT": ["LOGICAL_OPERATOR_PREFIX SPACE", "SPACE"], 

                # Loops
                "FOR_HEADER": ["FOR SPACE EXPRESSION_IDENTIFIER SPACE IN SPACE RANGE BRACKET_OPEN INITIAL COMMA SPACE FINAL COMMA SPACE STEP BRACKET_CLOSE SPACE COLON", 
                               "FOR SPACE EXPRESSION_IDENTIFIER SPACE IN SPACE RANGE BRACKET_OPEN INITIAL COMMA SPACE FINAL BRACKET_CLOSE SPACE COLON"],
                "INITIAL": ["DIGIT"],
            
                "FOR_LOOP": ["FOR_HEADER NEW_LINE TAB_INDENT DISPLAY"],
                "ADVANCED_FOR_LOOP": ["FOR_LOOP",
                                      "FOR_HEADER NEW_LINE TAB_INDENT ADVANCED_DISPLAY"],


                # While Loops

                # Definitions for relational operators
                "RELATIONAL_OPERATOR_LESS": [ "<", "<="],
                "RELATIONAL_OPERATOR_GREATER": [">", ">="],

                # Less than or equal conditions
                "CONDITION_EXPRESSION_LESS": [
                    "EXPRESSION_IDENTIFIER_WHILE SPACE RELATIONAL_OPERATOR_LESS SPACE FINAL_LESS"
                ],
                
                # Greater than or equal conditions
                "CONDITION_EXPRESSION_GREATER": [
                    "EXPRESSION_IDENTIFIER_WHILE SPACE RELATIONAL_OPERATOR_GREATER SPACE FINAL_GREATER"
                ],
            
                # While 
                "WHILE_HEADER_LESS": ["WHILE SPACE CONDITION_EXPRESSION_LESS SPACE COLON NEW_LINE"],
                "WHILE_LOOP_LESS": ["WHILE_HEADER_LESS TAB_INDENT DISPLAY NEW_LINE TAB_INDENT UPDATE_LESS"],
                "UPDATE_LESS": ["WHILE_IDENTIFIER SPACE EQUALS SPACE WHILE_IDENTIFIER SPACE + SPACE STEP"],
                
                "WHILE_HEADER_GREATER": ["WHILE SPACE CONDITION_EXPRESSION_GREATER SPACE COLON NEW_LINE"],
                "WHILE_LOOP_GREATER": ["WHILE_HEADER_GREATER TAB_INDENT DISPLAY NEW_LINE TAB_INDENT UPDATE_GREATER"],
                "UPDATE_GREATER": ["WHILE_IDENTIFIER SPACE EQUALS SPACE WHILE_IDENTIFIER SPACE - SPACE STEP"],
    
                # Displaying 
                "DISPLAY" : ["PRINT BRACKET_OPEN DISPLAY_IDENTIFIER BRACKET_CLOSE"],
                "ADVANCED_DISPLAY" : ["DISPLAY",
                                      "PRINT BRACKET_OPEN DISPLAY_EXPRESSION BRACKET_CLOSE"],


                "LEVEL1.1": ["IDENTIFIER_INITIALIZATION SIMPLE_ASSIGNMENTS ADVANCED_DISPLAY"],
                "LEVEL1.2": ["IDENTIFIER_INITIALIZATION ADVANCED_ASSIGNMENTS ADVANCED_DISPLAY"],
                "LEVEL2.1": ["IDENTIFIER_INITIALIZATION SIMPLE_IF_STATEMENT TAB_INDENT DISPLAY", 
                            "IDENTIFIER_INITIALIZATION SIMPLE_IF_STATEMENT TAB_INDENT DISPLAY NEW_LINE SIMPLE_ELIF_STATEMENT TAB_INDENT DISPLAY NEW_LINE ELSE_STATEMENT TAB_INDENT DISPLAY", 
                            "IDENTIFIER_INITIALIZATION SIMPLE_IF_STATEMENT TAB_INDENT DISPLAY NEW_LINE ELSE_STATEMENT TAB_INDENT DISPLAY"],
                "LEVEL2.2": ["IDENTIFIER_INITIALIZATION ADVANCED_ASSIGNMENTS ADVANCED_IF_STATEMENT TAB_INDENT ADVANCED_DISPLAY", 
                            "IDENTIFIER_INITIALIZATION ADVANCED_ASSIGNMENTS ADVANCED_IF_STATEMENT TAB_INDENT ADVANCED_DISPLAY NEW_LINE ADVANCED_ELIF_STATEMENT TAB_INDENT ADVANCED_DISPLAY NEW_LINE ELSE_STATEMENT TAB_INDENT ADVANCED_DISPLAY", 
                            "IDENTIFIER_INITIALIZATION ADVANCED_ASSIGNMENTS ADVANCED_IF_STATEMENT TAB_INDENT ADVANCED_DISPLAY NEW_LINE ELSE_STATEMENT TAB_INDENT ADVANCED_DISPLAY"],
                "LEVEL3.1": ["IDENTIFIER_INITIALIZATION FOR_LOOP"],
                "LEVEL3.2": ["IDENTIFIER_INITIALIZATION ADVANCED_ASSIGNMENTS ADVANCED_FOR_LOOP"],

                "LEVEL4.1": ["IDENTIFIER_INITIALIZATION WHILE_LOOP_LESS", "IDENTIFIER_INITIALIZATION WHILE_LOOP_GREATER"],
            
                "ALL": ["LEVEL1.1", "LEVEL1.2", "LEVEL2.1", "LEVEL2.2", "LEVEL3.1", "LEVEL3.2", "LEVEL4.1"],

            
                    }
        



    def generate_code(self, symbol, assigned_identifiers, last_variable, for_init_step, parent=None)->str:
        """
        Generate code recursively based on the context-free grammar rules.

        Parameters:
        - symbol (str): The symbol to generate code for.
        - assigned_identifiers (dict): Dictionary of assigned identifiers and their values.
        - last_variable (set): Set of the last used variables.
        - parent (Node): Parent node in the syntax tree.

        Returns:
        - str: The generated code.
        """
        node = Node(symbol, parent=parent)

        # If the symbol is a non-terminal <--> it's a production rule (PR)
        if symbol in self.cfg_rules:
            # We check if the PR is an IDENTIFIER_INITIALIZATION in which case we check if we didn't go past max_init initializations
            if symbol == "IDENTIFIER_INITIALIZATION":
                if self.init_count < self.max_init:
                    self.init_count += 1
                else:
                    symbol = "INITIALIZATION"
            # We developp the PR
            rule = random.choice(self.cfg_rules[symbol])
            symbols = rule.split(" ")
            # We call the generate code function to get the string associated with this PR
            generated_symbols = [self.generate_code(s, assigned_identifiers, last_variable, for_init_step, node) for s in symbols]
            # If it's an INITIAL=>DIGIT PR , we record the DIGIT=>0..255 value in the for_init_step dictionary (will be used when calculating the FINAL of the for loop)
            if symbol == "INITIAL":
                init = generated_symbols[0]
                for_init_step["initial_value"] = init
            # Elif it's an INITIALIZATION PR, we record the generated VARIABLE and it's DIGIT value in the assigned_identifiers dictionary
            elif symbol == "INITIALIZATION":
                variable_name = generated_symbols[0]
                variable_value = generated_symbols[4]  
                assigned_identifiers[variable_name] = variable_value
            # Elif it's a SIMPLE/ADVANCED_ASSIGNMENTS PR, we record the generated VARIABLE in the last_variable set (for it to be printed later ...)
            elif (symbol == "SIMPLE_ASSIGNMENTS") or (symbol == "ADVANCED_ASSIGNMENTS"):
                # We check if the SIMPLE/ADVANCED_ASSIGNMENTS PR didn't develop to "" (in which case it's just as if didn't exist ...)
                if generated_symbols[0]:
                    last_variable.add(generated_symbols[0])
            # Concatenate the generated_sub_codes and return the resulting sub_code
            return ''.join(generated_symbols)

        # Else the symbol is a (meta-)terminal, a terminal being one that is returned as is (the simplest case), and a meta-terminal must be generated based on past generations   
        # If EXPRESSION_IDENTIFIER (like we find in ASSIGNEMENTS, DISPLAYS, and FOR loops), we choose randomly among one of the previously initialized variables
        # NOTE: FOR loops don't require the control variable to be initialized -> this could be a point of generalization
        if symbol == "EXPRESSION_IDENTIFIER":
            identifier = random.choice(tuple(assigned_identifiers.keys())) if assigned_identifiers else random.choice(self.cfg_rules["DIGIT"])
            return identifier
        # If EXPRESSION_IDENTIFIER_WHILE (i.e. "the declaration" of the control variable of the while loop)
        # NOTE: this one contrary to for loop ... must be one of the existing initialized variables
        if symbol == "EXPRESSION_IDENTIFIER_WHILE":
            initial_var = random.choice(tuple(assigned_identifiers.keys())) if assigned_identifiers else random.choice(self.cfg_rules["DIGIT"])
            for_init_step["initial_var"] = initial_var
            for_init_step["initial_value"] = assigned_identifiers[initial_var]
            return initial_var    
        # If WHILE_IDENTIFIER (i.e. the "update" of the control variable of the while loop), get it from the for_init_step dictionary (filled by the EXPRESSION_IDENTIFIER_WHILE meta-terminal)
        if symbol == "WHILE_IDENTIFIER":
            return for_init_step.get("initial_var", "*")
        # If the symbol is a FINAL (for the for loop) or FINAL_LESS (for the while <= loop), choose a step and number of executions, compute the FINAL/_LESS using the for_init_step dict, and record the setp for the for loop as it will be needed later to fill the STEP meta-terminal
        if (symbol == "FINAL") or (symbol == "FINAL_LESS"):    
            initial_value = for_init_step.get("initial_value", "0")
            # Generate valid step_value and execution_count
            valid_values = [(1, 2), (2, 1), (2, 2), (2, 3), (3, 2)]
            step_value, execution_count = random.choice(valid_values)
            for_init_step["step"] = str(step_value)
            final_value = step_value * execution_count + int(initial_value) - 1
            return str(final_value)
        # Same thing as for the one before but this one is only meant for the while loop
        if symbol == "FINAL_GREATER":
            initial_value = for_init_step.get("initial_value", "0")
            # Generate valid step_value and execution_count
            valid_values = [(1, 2), (2, 1), (2, 2), (2, 3), (3, 2)]
            step_value, execution_count = random.choice(valid_values)
            for_init_step["step"] = str(step_value)
            final_value = int(initial_value) - step_value * execution_count + 1
            return str(final_value)
        # If the STEP meta variable, fill it with the for_init_step dict  
        if symbol == "STEP":
            return for_init_step.get("step", "0")
        # If DISPLAY_IDENTIFIER, fill it with either the last variable (if there was an ASSIGNEMENTS), or any randomly chosen variable 
        if symbol == "DISPLAY_IDENTIFIER":
            try:
                return f"{tuple(last_variable)[0]}"
            except:
                return f"{random.choice(tuple(assigned_identifiers.keys()))}"
        # If non of the above i.e. its a terminal (not a meta-terminal)
        return symbol

    
    

    def print_tree(self, root):
        """
        Print the syntax tree using the RenderTree utility from the anytree module.

        Parameters:
        - root (Node): The root node of the syntax tree.
        """
        for pre, _, node in RenderTree(root):
            print(f"{pre}{node.name}")

    def generate_program(self, level):
        """
        Generate a program based on the specified level.

        Parameters:
        - level (str): The level of the program.

        Returns:
        - Tuple[Node, str]: The syntax tree root node and the generated program.
        """
        # assigned = set()
        assigned = {}
        last_variable = set()
        for_init_step = {}
        root = Node("ROOT")

        self.init_count = 0
        if level == "1.1":
            self.max_init = 2
        elif level == "1.2":
            self.max_init = 3
        elif level == "2.1":
            self.max_init = 2
        elif level == "3.1":
            self.max_init = 2
        elif level == "3.2":
            self.max_init = 4
        elif level == "4.1":
            self.max_init = 2
        else:
            self.max_init = 5
            
        if level == "ALL" :
            level_passed = level
        else :
            level_passed = "LEVEL" + level
            
        program = self.generate_code(symbol = level_passed,
                                     assigned_identifiers = assigned,
                                     last_variable = last_variable,
                                     for_init_step = for_init_step,
                                     parent = root)
        
        return root, program.replace("SPACE", " ")
    
    def memory_usage(self):
        process = psutil.Process(os.getpid())
        mem_info = process.memory_info()
        return mem_info.rss

    def generate_and_write_programs(self, num_programs, level, filename='data.txt', deduplicate=True):
        """
        Generate and write a specified number of programs to a file.

        Parameters:
        - num_programs (int): Number of programs to generate and write.
        - level (str): The level of the programs.
        - filename (str): Name of the file to write the programs (default is 'data.txt').
        - deduplicate (bool, optional): Whether to perform deduplication of generated programs (default is True).
        """
        start_time = time.time()  
        start_mem = self.memory_usage()
        max_tries = 1000
        num_tries = 0
        
        with open(filename, 'w') as file:
            
            generated_programs = 0
            hashes = set() 
            pbar = tqdm(desc="Generation", total=num_programs)
            while generated_programs < num_programs:
                try:
                    root, program = self.generate_program(level)
                    code = program + "\n# output"

                    SIO = StringIO()
                    with redirect_stdout(SIO):
                        exec(code)
                    output = SIO.getvalue().strip()

                    output = '\n'.join([f'# {line}' if line else f'# ' for line in output.split('\n')])
                    result = f"""{code}\n{output}"""
                    
                    program_hash = hashlib.sha256(result.encode('utf-8')).hexdigest()

                    if deduplicate:
                        if program_hash not in hashes:
                            hashes.add(program_hash)
                            file.write(result + '\n\n')
                            generated_programs += 1  
                            pbar.update(1)
                            num_tries = 0
                        else:
                            num_tries += 1
                            if num_tries >= max_tries:
                                print("Hit max tries in deduplication, stopping generation.")
                                break
                    else:
                        file.write(result + '\n\n')
                        
                        generated_programs += 1  
                        pbar.update(1)
                except Exception as e:
                    continue

        pbar.close()
        end_time = time.time()
        end_mem = self.memory_usage()
        deduplication_info = "with deduplication" if deduplicate else "without deduplication"
        print(f"Code generation completed in {end_time - start_time:.2f} seconds.")
        print(f"Memory used during code generation: {end_mem - start_mem} bytes")
        print(f"Generated {generated_programs} {'unique ' if deduplicate else ''}programs {deduplication_info}.")
        print(f"Programs are saved to {filename}.")


def main():
    parser = argparse.ArgumentParser(description='Generate and write programs based on a specified level. ')
    parser.add_argument('--num_programs', type=int, default=1000, help='Number of programs to generate and write (default is 1000)')
    parser.add_argument('--level', default="ALL", help='The level of the programs (1.1, 1.2, 2.1, 2.2, 3.1, 3.2, 4.1, ALL)')
    parser.add_argument('--filename', default='data.txt', help='Name of the file to write the programs (default is data.txt)')
    parser.add_argument('--deduplicate', action='store_true', default=True, help='Perform deduplication of generated programs (default is True)')

    args = parser.parse_args()

    code_generator = CodeGenerator()
    code_generator.generate_and_write_programs(num_programs=args.num_programs, level=args.level, filename=args.filename,  deduplicate=args.deduplicate)

if __name__ == "__main__":
    main()
