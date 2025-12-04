import json
import threading

class ThreadSafeJSONLWriter:
    def __init__(self, filename):
        self.filename = filename
        self.lock = threading.Lock()
        open(filename, 'w').close()
    
    def write(self, data):
        with self.lock:
            with open(self.filename, 'a', encoding='utf-8') as f:
                f.write(json.dumps(data, ensure_ascii=False) + '\n')
                f.flush()