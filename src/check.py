from pathlib import Path
from agent_mcp import lean_check
import argparse

if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('filename')  
    args = parser.parse_args()
    filename = args.filename
    code = Path(filename).read_text(encoding="utf-8")
    result = lean_check(code, timeout=60)
    print(result)