#!./python
import pandas as pd
import re
from tabulate import tabulate
from pathlib import Path


# Extracting <Logic>/<Bench>/<Sample> from '../proofs/' in Command column
def extract_proof_info(command):
    match = re.search(r'\.\./proofs/([^/]+)/([^/]+)/(.+?)(\s|;|$)', command)
    if match:
        return match.group(1), match.group(2), match.group(3)
    return None, None, None

def extract_proof_info_alethe(command):
    # Regex to match the elaborate path in ../run/alethe/ or ../benchs/
    match = re.search(r'(?:../run/alethe|../benchs)/([^/]+)/([^/]+)/(.+?)(?:\s|;|$)', command)
    
    if match:
        logic = match.group(1)
        bench = match.group(2)
        name = f"{logic}/{bench}/{match.group(3)}"
        return logic, bench, name
    
    return None, None, None

def extract_proof_info_convert(command):
    # Improved regex to capture logic, bench, and name
    match = re.search(r'\.\./convert/([^/]+)/([^/]+)/(.+?)(?:\s|;|$)', command)
    
    if match:
        logic = match.group(1)
        bench = match.group(2)
        name = f"{logic}/{bench}/{match.group(3)}"
        return logic, bench, name
    
    return None, None, None
# Extracting the path after 'lambdapi check ' in Command column
def extract_proof_info_lambdapi(command):
    match = re.search(r"lambdapi check ['\"]?([^/]+)/([^/]+)/(.+?)\.lp['\"]?", command)
    if match:
        return match.group(1), match.group(2), f"{match.group(1)}/{match.group(2)}/{match.group(3)}"
    return None, None, None


def get_stat(file_path,extract_fun):
    df = pd.read_csv(file_path, delimiter='\t', engine='python', names=['Seq', 'Host', 'Starttime', 'JobRuntime', 'Send', 'Receive', 'Exitval', 'Signal', 'Command'])
    # Convert Exitval column to int
    df['Exitval'] = pd.to_numeric(df['Exitval'], errors='coerce').fillna(0).astype(int)
    df['Signal'] = pd.to_numeric(df['Signal'], errors='coerce').fillna(0).astype(int)

    df.loc[(df['Exitval'] == -1) & (df['Signal'] == 15), 'Exitval'] = 143

    df[['Logic', 'Bench', 'Name']] = df['Command'].apply(lambda x: pd.Series(extract_fun(x)))

    data_structure = df.to_dict(orient='records')

    exitval_counts = df.groupby(['Bench', 'Exitval']).size().unstack(fill_value=0)

    exitval_counts.rename(columns={
        0: 'Success',
        1: 'Error',
        134: 'Abort (SIGABRT)', # CVC5 Abort proof production
        101: 'Rust Panick', # exit code return by panic!() in Rust (for Carcara)
        143: 'Terminated (SIGTERM)' # GNU parallel kill the process with SIGTERM if timeout is reach 
    }, inplace=True)

    return tabulate(exitval_counts.reset_index(), headers='keys', tablefmt="fancy_grid", floatfmt=".3f", showindex=False) # showindex add the index column


if __name__ == '__main__':
    if Path('joblogs/cvc5.txt').is_file():
        cvc5_get_proof_result = get_stat('joblogs/cvc5.txt',extract_proof_info)
        print("CVC5 get-proof results\n")
        print(cvc5_get_proof_result)

    if Path('joblogs/elab_logs.txt').is_file(): 
        elaboration_result = get_stat('joblogs/elab_logs.txt',extract_proof_info_alethe)
        print("\nCarcara elaboration results:\n")
        print(elaboration_result)

    if Path('joblogs/translate_logs.txt').is_file(): 
        translation_result = get_stat('joblogs/translate_logs.txt',extract_proof_info_convert)
        print("\nTranslation results:\n")
        print(translation_result)

    if Path('joblogs/lambdapi-checks.txt').is_file(): 
        check_result = get_stat('joblogs/lambdapi-checks.txt',extract_proof_info_lambdapi)
        print("\nLambdapi check results:\n")
        print(check_result)
