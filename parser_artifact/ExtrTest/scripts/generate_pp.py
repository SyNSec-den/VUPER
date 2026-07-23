import re

# Input and output file paths
module_name = "FormatTest"  # Replace with the actual module name

input_file = f"src/{module_name}.mli"  # Replace with your .mli file
print_output_file = "src/FormatPrint.ml"  # The generated output file
json_output_file = "src/FormatJson.ml" # the json file

unchange_set =  {"coq_Buffer", "coq_Pos", "coq_ElementTypeParam__Type", "coq_SetupRelease__Type", "coq_SetupRelease__Format_Type", "coq_SetupRelease__g", "__", "typ_set", "choice", "choice_ext", "seq_elem", "seq_type", "seq_ext_type", "seq_elem_to_type", "ext_elem_to_type", "typ", "get_formats", "get_serial_prod", "get_parse_prod", "get_to_len_prod", "seq_elem_to_set", "seq_elem_to_serial", "seq_elem_to_parse", "seq_elem_to_format", "seq_format_prod", "seq_serial_prod", "seq_to_len_prod", "seq_parse_prod", "three_split", "coq_P_Type", "nat_T"}

bit_string_yojson_def = '''
type bit_string = [%import: FormatTest.bit_string] 
let bit_string_to_jer (bs : bit_string) =
  DebugPrint.hex_of_bit_string bs
'''

bit_string_fixed_yojson_def = '''
type bit_string_fixed = [%import: FormatTest.bit_string_fixed] 
let bit_string_fixed_to_jer (bs : bit_string_fixed) =
  DebugPrint.hex_of_bit_string_fixed bs
'''


octet_string_yojson_def = '''
type octet_string = [%import: FormatTest.octet_string]
let octet_string_to_jer (lb : octet_string) =
  `String (DebugPrint.hex_of_byte_list lb)
'''

char_list_yojson_def = '''
type char_list = [%import: FormatTest.char_list]
let char_list_to_jer (lb : char_list) =
  `String (DebugPrint.string_of_char_list lb)
'''

option_yojson_def = '''
let option_to_jer (a_to_jer : 'a -> Yojson.Safe.t) (x : 'a option) : Yojson.Safe.t =
  match x with
  | None -> `Null
  | Some v -> a_to_jer v
'''

sum_yojson_def = '''
type ('a, 'b) sum = [%import: ('a, 'b) FormatTest.sum]
let sum_to_jer (a_to_jer : 'a -> Yojson.Safe.t)
    (b_to_jer : 'b -> Yojson.Safe.t) (z : ('a, 'b) sum) : Yojson.Safe.t =
    match z with
    | Inl v -> a_to_jer v
    | Inr v' -> b_to_jer v'
'''

setup_release_def = '''
type 'elementTypeParam__Type setupRelease__Type = [%import: 'elementTypeParam__Type  FormatTest.setupRelease__Type]
let setupRelease__Type_to_jer
    (elementTypeParam__Type_to_jer : 'elementTypeParam__Type -> Yojson.Safe.t)
    (x : 'elementTypeParam__Type setupRelease__Type) =
  match x with
  | SetupRelease__release () -> `Null
  | SetupRelease__setup v -> `Assoc [("setup", elementTypeParam__Type_to_jer v)]
'''

def is_type_definition(line):
    """Check if the line starts a type definition."""
    return re.match(r"^\s*type\s+\w+", line)

def rewrite_type_definition(line, derive):
    """
    Rewrite type definitions to refer back to the original module.
    Example:
      Input: type x = y
      Output: type x = Definitions.x [@@deriving jer]
    """
    # Match `type x = <definition>`
    match = re.match(r"^\s*type\s+(\w+)\s*=", line.strip())

    # problem here is we might not able to capture sum type
    if match:
        (type_name, ) = match.groups()
        if (type_name == "bit_string"):
            rewritten = bit_string_yojson_def
            return rewritten + "\n"

        if (type_name == "bit_string_fixed"):
            rewritten = bit_string_fixed_yojson_def
            return rewritten + "\n"

        if (type_name == "octet_string"):
            rewritten = octet_string_yojson_def
            return rewritten + "\n"

        # another case is 'char list'
        if (type_name == "char_list"):
            rewritten = char_list_yojson_def
            return rewritten + "\n"
        
        # here we need to remove coq_buffer, coq_Pos and __
        if (not ((type_name in unchange_set) or type_name.endswith("Format_Type") or type_name.endswith("list_type"))) :
            # Rewrite to reference the original module
            rewritten = f"type {type_name} = [%import: {module_name}.{type_name}] [@@deriving {derive}]"
            return rewritten + "\n"
    return ""

# we also want to be able to generate json representations
# here the function f will dictate which
def generate_printers(input_file, output_file, derive):
    """Generate a file with pretty-printing functions."""
    with open(input_file, "r") as infile, open(output_file, "w") as outfile:
        # Write header
        outfile.write("(* Auto-generated file for pretty-printing types *)\n")
        # outfile.write(f"open {module_name}\n\n")  # Adjust to the module name
        # For sum type & setup release type (any dependent type)
        
        outfile.write(option_yojson_def)
        outfile.write(sum_yojson_def)
        outfile.write(setup_release_def)

               
        for line in infile:
            if is_type_definition(line):
                # Rewrite type definitions to reference the original module
                outfile.write(rewrite_type_definition(line, derive))
            else:
                pass
                # Write non-type lines as is
                #outfile.write(line)

    print(f"Generated file: {output_file}")

    
# Run the script
if __name__ == "__main__":
    # generate_printers(input_file, print_output_file, "show")
    generate_printers(input_file, json_output_file, "jer")
