import nr_test
import json
import pycrate_asn1rt.asnobj_construct as ac
import pycrate_asn1rt.asnobj_basic as ab
import pycrate_asn1rt.asnobj_str as astr

import sys
import re
from deepdiff import DeepDiff


def remove_extra_brace_pairs(json_str):
    """
    Removes extra consecutive brace pairs.
    It finds occurrences of '{{ ... }}' and replaces them with '{ ... }'.
    The substitution is performed recursively.
    """
    # This pattern matches two consecutive '{' then any (non-greedy) content, then two consecutive '}'.
    pattern = re.compile(r'\{\{(.*?)\}\}')
    # Recursively substitute while such a pair exists in the string.
    while pattern.search(json_str):
        json_str = pattern.sub(r'{\1}', json_str)
    return json_str


# Here, I am given a message, that is mapped to json,
# then given this information, and the structure of the ul-dcch-message
# we can modify the message.

# here obj is a dictionary, fmt is the pycrate ASN.1 object
def norm_to_srs_format(obj, fmt):
    
    # in the case it is a SEQUENCE, it should be normal, but we do need to
    # modify each field. 
    if isinstance(fmt, ac.SEQ):
        # the object should be a dict
        if isinstance(obj, dict):
            new_obj = {}
            for k, v in obj.items():
                # first for the ones in extensions, we need to pick them out
                if re.match(r"^ext\d+$", k):
                    # we need to look into this
                    if (isinstance(v, dict)):
                        for k1, v1 in v.items():
                            fmt_k = fmt._cont[k1]
                            new_obj[k1] = norm_to_srs_format(v1, fmt_k)
                            
                        continue

                
                fmt_k = fmt._cont[k]
                if isinstance(fmt_k, astr.OCT_STR):
                    # if the object is an empty string, and when it is an OPTIONAL
                    # fmt.opt = True we ignore it
                    if (isinstance(v, str)) and fmt_k._opt:
                        if not v:
                            continue
                # consider the problem with setup release
                elif isinstance(fmt_k, ac.CHOICE):
                    if (fmt_k._tr == nr_test.EUTRA_RRC_Definitions.SetupRelease):
                        # we know there are two choices, release or setup
                        # if release then it is NULL
                        k1, v1 = list(v.items())[0]
                        if k1 == "release":
                            pass
                        else: 
                            new_obj[k] = norm_to_srs_format(v1, fmt_k._cont["setup"])

                        continue
                        
                new_obj[k] = norm_to_srs_format(v, fmt_k)
                
            return new_obj
        
    # Now, consider the CHOICE case
    elif isinstance(fmt, ac.CHOICE):
        if isinstance(obj, dict):
            new_obj = {}
            k, v = list(obj.items())[0]

            # now if the value is a empty sequence, or a NULL
            # then we simply ignore it
            
            fmt_k = fmt._cont[k]
            if isinstance(fmt_k, ac.SEQ):
                # and it has no items
                if not fmt_k._cont:
                    return new_obj
            elif isinstance(fmt_k, ab.NULL):
                return new_obj
            elif isinstance(fmt_k, ab.ENUM):
                # if enum only has 1 item, it is also ignored in CHOICE
                if len(fmt_k._cont) == 1:
                    return new_obj

            new_obj[k] = norm_to_srs_format(v,  fmt._cont[k])
            return new_obj

    # if it is a list, then we just access all the items
    elif isinstance(fmt, ac.SEQ_OF):
        if isinstance(obj, list):
            new_obj = []

            for v in obj:
                new_obj.append( norm_to_srs_format(v, fmt._cont) )

            return new_obj

        
    else:
        return obj



all_input = sys.stdin.read()
#print(all_input)
input_dict = json.loads( remove_extra_brace_pairs(all_input) )

vp_dict = input_dict["vp"]
srs_dict = input_dict["srs"]

# we first compare if each of them failed or not.
result = True
if (vp_dict == "Error"):
    if srs_dict == "Error":
        pass
    else:
        result = False
        #print("srs Correct while vp ERROR")
else:
    if srs_dict == "Error":
        result = False
        #print("srs ERROR while vp Correct")
    else:
        normed_vp_dict = norm_to_srs_format( vp_dict, nr_test.EUTRA_RRC_Definitions.DL_DCCH_MessageType)
        result = (srs_dict[0]["DL-DCCH-Message"]["message"] == normed_vp_dict)

        #if (result == False): 
        #    print(srs_dict)
        #    print(vp_dict)
        #    diff = DeepDiff(srs_dict[0]["UL-DCCH-Message"]["message"], normed_vp_dict)
        #    print("Difference is: ")
        #    print(diff)

            
print(result)

#if (result == False):
#   print()
