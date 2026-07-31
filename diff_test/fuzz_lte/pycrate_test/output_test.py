import nr_test
import afl
import sys
import subprocess
import json 
import re

#from deepdiff import DeepDiff


#afl.init()

import os

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
        
    #    return obj.hex()
            
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


folder_path =  "fuzzing-results/run4/default/crashes/"

# "../../test_cases/queue/"

idx = 0

#for filename in os.listdir(folder_path):

if True:
    #file_path = os.path.join(folder_path, filename)
    
    #if os.path.isfile(file_path):  # Ensure it's a file
        #with open(file_path, 'rb') as file:
    if True:
        if True:
            #print(file_path) 
            #data = file.read()  # Read as bytes

            data = sys.stdin.buffer.read()

            print(f"Reading data {data.hex()}")
            
            #print(f"Contents of {filename} (bytes):\n{content[:100]}...\n")  # Print first 100 bytes for preview
            ocaml_result = subprocess.run(["./../verified_format/_build/default/test/test.exe"], input=data, text=False, capture_output=True)
            ocaml_str = ocaml_result.stdout.decode()

            ocaml_error = 0;
            ocaml_dict = {}
    
            if ocaml_str == "\"Error\"":
                ocaml_error = 1

            else:
                ocaml_dict = json.loads(ocaml_str)
            
                
            dl_dcch = nr_test.EUTRA_RRC_Definitions.DL_DCCH_Message
            dl_dcch.from_uper(data)
    
            try:
                #sys.stdout = open(os.devnull, 'w')

               pass
                # Restore stdout to normal
                #sys.stdout = sys.__stdout__

            except Exception as e:
                print(f"python error as {e}")
                
                # here print the exception
                if (ocaml_error == 1):
                    #pass
                    print(f"cause error {e}!")

                    
                else:
                    print(f"{filename} causes python error but not ocaml error")
                    print(ocaml_dict)
                    #idx += 1
                           
            else:
                print("python accept")
                if (ocaml_error == 1):

                    # here pycrate accepts unknown choice or enum extensions
                    # so we need to manually rule out this case

                    # Note that we need to distinguish between choice extension
                    # and sequence extension
                    try:
                        pycrate_dict = tuple_to_dict_c(dl_dcch())

                    except:
                        print(f"{filename} causes ocaml error but not python error")
                        # as if we automatically reject the message
                        
                    else:
                        #print(f"{filename} causes ocaml error but not python error")
                        #pass
                        print(dl_dcch())

                        print(dir(dl_dcch))
                        
                        print(dl_dcch._struct.show())

                        
                        print(f"new encoding should be {dl_dcch.to_uper().hex()}")
                        #idx += 1

                else:

                    print("pycrate result is : ", dl_dcch())

                    try:
                        pycrate_dict = (json.loads(dl_dcch.to_jer())['message'])
                    except:
                    
                        pycrate_dict = tuple_to_dict(dl_dcch())
                        pycrate_dict = (json.loads(dl_dcch.to_jer(pycrate_dict))['message'])
                        
                    

                    ocaml_dict = merge_ext_keys(ocaml_dict)
        
                    if (ocaml_dict != pycrate_dict):
                        diff = DeepDiff(ocaml_dict, pycrate_dict)
                        print(f"{filename} causes difference in decoding")
                        print(diff)
                        print(ocaml_dict)
                        #print(pycrate_dict)

                        print("\n")
                        #idx += 1
                    
                    # we try to re encode the message and print it
                    print("its real encoding should be: ", dl_dcch.to_uper().hex())

