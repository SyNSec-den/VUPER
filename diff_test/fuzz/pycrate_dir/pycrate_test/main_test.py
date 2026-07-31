import nr_test
import afl
import sys
import subprocess
import json
import re

#from deepdiff import DeepDiff


#afl.init()

def tuple_to_dict(obj):
    if isinstance(obj, tuple) and len(obj) == 2:  # Convert only 2-element tuples
        key, value = obj
        if isinstance(key, str):
            return (key, tuple_to_dict(value))  # Recursively process value
        else:
            return obj
            
    elif isinstance(obj, list):  # Keep lists, but process their elements
        return [tuple_to_dict(item) for item in obj]
    elif isinstance(obj, dict):  # Process dictionaries recursively
        # remove unknown extensions
        return {k: tuple_to_dict(v) for k, v in obj.items() if not re.fullmatch(r'_ext_\d+', k)}
    #elif isinstance(obj, bytes): # turn bytes into strings
    #    return obj.hex()
            
    return obj  # Return as-is for other types


def tuple_to_dict_c(obj):
    if isinstance(obj, tuple) and len(obj) == 2:  # Convert only 2-element tuples
        key, value = obj
        if isinstance(key, str):
            # again if the key indicates its an unknown choice extension,
            # we remove it
            if re.fullmatch(r'_ext_\d+', key):
                raise Exception ("Reject Unknown Choice.")
            
            return (key, tuple_to_dict_c(value))  # Recursively process value
        else:
            return obj
            
    elif isinstance(obj, list):  # Keep lists, but process their elements
        return [tuple_to_dict_c(item) for item in obj]
    elif isinstance(obj, dict):  # Process dictionaries recursively
        # remove unknown extensions
        return {k: tuple_to_dict_c(v) for k, v in obj.items() if not re.fullmatch(r'_ext_\d+', k)}
    elif isinstance(obj, str):
        if re.fullmatch(r'_ext_\d+', obj):
            # in the case where
            raise Exception ("Reject Unknown Enum.")

    return obj  # Return as-is for other types

        
def merge_ext_keys(obj):
    if isinstance(obj, dict):  
        merged_dict = {}  # New dictionary to store merged results
        
        for key, value in obj.items():
            if re.fullmatch(r'ext\d+', key) and isinstance(value, dict):
                # Merge "extX" dictionary contents into merged_dict
                for k, v in value.items():
                    merged_dict[k] = merge_ext_keys(v)
            else:
                merged_dict[key] = merge_ext_keys(value)

        return merged_dict

    elif isinstance(obj, list):  
        # Process lists by applying the function recursively to each element
        return [merge_ext_keys(item) for item in obj]

    return obj  # Base case: return non-dict, non-list values as-is


while afl.loop(5000):

    data = sys.stdin.buffer.read()
        
    # run ocaml code
    ocaml_result = subprocess.run(["./../ocaml_test/_build/default/test/test.exe"], input=data, text=False, capture_output=True)
    ocaml_str = ocaml_result.stdout.decode()

    ocaml_error = 0;
    ocaml_dict = {}
    
    if ocaml_str == "\"Error\"":
        ocaml_error = 1;
    else:
        ocaml_dict = json.loads(ocaml_str)

    
    dl_dcch = nr_test.NR_RRC_Definitions.DL_DCCH_Message

    
    try:
        dl_dcch.from_uper(data)
    except:
        if (ocaml_error == 1):
            continue
        else:
            raise Exception("Fail")
        
    else:
        if (ocaml_error == 1):
            try:
                pycrate_dict = tuple_to_dict_c(dl_dcch())

            except:
                continue
            else:
                raise Exception("Fail")

        try:
            pycrate_dict = (json.loads(dl_dcch.to_jer())['message'])
        except:
            pycrate_dict = tuple_to_dict(dl_dcch())
            pycrate_dict = (json.loads(dl_dcch.to_jer(pycrate_dict))['message'])
                        
        ocaml_dict = merge_ext_keys(ocaml_dict)

        if (ocaml_dict == pycrate_dict):
            # all good
            print(dl_dcch())
            print("Same")
            continue
        else:
            diff = DeepDiff(ocaml_dict, pycrate_dict)
            print(diff)
            #raise Exception("Fail")
        
    sys.stdin.seek(0)    
