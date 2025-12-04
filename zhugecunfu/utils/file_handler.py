"""File handling utilities."""
import json
from typing import List, Dict, Any
from utils.logger_setup import setup_logger

logger = setup_logger(__name__)

def load_jsonl(file_path: str) -> List[Dict[str, Any]]:
    """Load problems from a JSONL file."""
    problems = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line_num, line in enumerate(f, 1):
            try:
                data = json.loads(line.strip())
                problems.append(data)
            except json.JSONDecodeError as e:
                logger.error(f"Error parsing line {line_num}: {e}")
                continue
    return problems

def save_jsonl(data: List[Dict[str, Any]], file_path: str) -> None:
    """Save results to a JSONL file."""
    with open(file_path, 'w', encoding='utf-8') as f:
        for item in data:
            f.write(json.dumps(item, ensure_ascii=False) + '\n')

def select_top_n(problems: List[Dict[str, Any]], n: int) -> List[Dict[str, Any]]:
    """Select only the top n questions from the list."""
    if n <= 0:
        return []
    return problems[:n]