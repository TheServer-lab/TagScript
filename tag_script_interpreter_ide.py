"""
TagScript Interpreter + Simple GUI IDE
File: TagScript_interpreter_ide.py

Run: python TagScript_interpreter_ide.py
"""
import ast
import operator
import importlib
import importlib.util
import io
import os
import queue
import re
import sys
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk

# -----------------------------
# Simple TagScript AST node
# -----------------------------
class TSNode:
    def __init__(self, tag, attrib=None, text=None, children=None):
        self.tag = tag
        self.attrib = attrib or {}
        self.text = text or ''
        self.children = children or []

    def __repr__(self):
        return f"<TSNode {self.tag} attrib={self.attrib} text={repr(self.text)} children={len(self.children)}>"

# -----------------------------
# Utility: safe expression evaluator
# -----------------------------
class SafeEvaluator:
    """
    Safe expression evaluator for TagScript using AST.
    Works on Python 3.8+ (uses ast.Constant). Blocks function calls and attribute access.
    Accepts env (variables dict) and extras (extra names like math/time).
    """

    KEYWORD_MAP = {
        'both': 'and',
        'either': 'or',
        'notreally': 'not'
    }

    ALLOWED_NODES = (
        ast.Expression,
        ast.BinOp,
        ast.UnaryOp,
        ast.BoolOp,
        ast.Compare,
        ast.Name,
        ast.Load,
        ast.Constant,
        ast.List,
        ast.Tuple,
        ast.Dict,
        ast.Subscript,
        ast.Slice,
    )

    ALLOWED_BINOPS = {
        ast.Add: operator.add,
        ast.Sub: operator.sub,
        ast.Mult: operator.mul,
        ast.Div: operator.truediv,
        ast.Mod: operator.mod,
        ast.Pow: operator.pow,
        ast.FloorDiv: operator.floordiv,
    }

    ALLOWED_UNARY = {
        ast.UAdd: operator.pos,
        ast.USub: operator.neg,
        ast.Not: operator.not_,
    }

    SAFE_BUILTINS = {
        'len': len,
        'int': int,
        'float': float,
        'str': str,
        'bool': bool,
        'min': min,
        'max': max,
        'abs': abs,
        'range': range,
        'list': list,
        'dict': dict,
        'sorted': sorted,
    }

    def __init__(self, env=None, extras=None):
        self.env = env or {}
        self.extras = extras or {}

    def _preprocess(self, expr: str) -> str:
        # Replace caveman keywords with Python keywords (word-boundary approach)
        s = str(expr)
        for k, v in self.KEYWORD_MAP.items():
            s = re.sub(rf'\b{k}\b', v, s)
        return s

    def eval(self, expr):
        if expr is None:
            return None
        # if primitive already
        if isinstance(expr, (int, float, bool, list, dict, tuple, str)):
            return expr
        s = str(expr).strip()
        s = self._preprocess(s)
        try:
            node = ast.parse(s, mode='eval')
        except Exception as e:
            raise RuntimeError(f"Expression parse error: {e} -- '{s}'")
        return self._eval_node(node.body)

    def _eval_node(self, node):
        if not isinstance(node, self.ALLOWED_NODES):
            raise RuntimeError(f"Disallowed expression element: {type(node).__name__}")

        if isinstance(node, ast.Constant):
            return node.value

        if isinstance(node, ast.Name):
            name = node.id
            if name in self.env:
                return self.env[name]
            if name in self.extras:
                return self.extras[name]
            if name in self.SAFE_BUILTINS:
                return self.SAFE_BUILTINS[name]
            raise RuntimeError(f"Unknown name '{name}' in expression")

        if isinstance(node, ast.BinOp):
            left = self._eval_node(node.left)
            right = self._eval_node(node.right)
            op_type = type(node.op)
            if op_type in self.ALLOWED_BINOPS:
                return self.ALLOWED_BINOPS[op_type](left, right)
            raise RuntimeError(f"Binary op {op_type} not allowed")

        if isinstance(node, ast.UnaryOp):
            operand = self._eval_node(node.operand)
            op_type = type(node.op)
            if op_type in self.ALLOWED_UNARY:
                return self.ALLOWED_UNARY[op_type](operand)
            raise RuntimeError(f"Unary op {op_type} not allowed")

        if isinstance(node, ast.BoolOp):
            if isinstance(node.op, ast.And):
                return all(self._eval_node(v) for v in node.values)
            if isinstance(node.op, ast.Or):
                return any(self._eval_node(v) for v in node.values)
            raise RuntimeError("Unsupported boolean operator")

        if isinstance(node, ast.Compare):
            left = self._eval_node(node.left)
            for op, comp in zip(node.ops, node.comparators):
                right = self._eval_node(comp)
                if isinstance(op, ast.Eq):
                    ok = (left == right)
                elif isinstance(op, ast.NotEq):
                    ok = (left != right)
                elif isinstance(op, ast.Gt):
                    ok = (left > right)
                elif isinstance(op, ast.Lt):
                    ok = (left < right)
                elif isinstance(op, ast.GtE):
                    ok = (left >= right)
                elif isinstance(op, ast.LtE):
                    ok = (left <= right)
                else:
                    raise RuntimeError("Unsupported comparison operator")
                if not ok:
                    return False
                left = right
            return True

        if isinstance(node, (ast.List, ast.Tuple)):
            return [self._eval_node(e) for e in node.elts]

        if isinstance(node, ast.Dict):
            keys = [self._eval_node(k) for k in node.keys]
            vals = [self._eval_node(v) for v in node.values]
            return dict(zip(keys, vals))

        if isinstance(node, ast.Subscript):
            val = self._eval_node(node.value)
            # handle simple index/slice
            if isinstance(node.slice, ast.Slice):
                # not fully-featured; evaluate bounds if present
                lower = self._eval_node(node.slice.lower) if node.slice.lower else None
                upper = self._eval_node(node.slice.upper) if node.slice.upper else None
                return val[lower:upper]
            else:
                idx = self._eval_node(node.slice)
                return val[idx]

        if isinstance(node, ast.Call):
            raise RuntimeError("Function calls are not allowed in expressions")

        if isinstance(node, ast.Attribute):
            raise RuntimeError("Attribute access is not allowed in expressions")

        raise RuntimeError(f"Unsupported expression node: {type(node).__name__}")

# -----------------------------
# TagScript: forgiving parser (not strict XML)
# -----------------------------
_TAG_RE = re.compile(r'<\s*(/)?\s*([a-zA-Z0-9_.-]+)([^>]*)>', re.DOTALL)
_ATTR_RE = re.compile(r'([a-zA-Z_:][-a-zA-Z0-9_:.]*)\s*=\s*("(?:[^"]*)"|\'(?:[^\']*)\')')

def parse_tagscript(source: str) -> TSNode:
    """
    Parse TagScript source into a TSNode tree.
    Accepts:
      - <tag attr="val"> ... </tag>
      - <tag attr="val" />
      - raw text
    Attributes must be quoted.
    This parser is forgiving (not strict XML).
    """
    pos = 0
    root = TSNode('root', {}, '')
    stack = [root]
    length = len(source)

    while pos < length:
        m = _TAG_RE.search(source, pos)
        if not m:
            # remaining text
            text = source[pos:]
            if text:
                stack[-1].children.append(TSNode('#text', {}, text))
            break
        start, end = m.span()
        if start > pos:
            text = source[pos:start]
            if text:
                stack[-1].children.append(TSNode('#text', {}, text))
        closing = bool(m.group(1))
        tagname = m.group(2)
        attrtext = m.group(3).strip()
        # determine self-closing by presence of trailing '/'
        self_close = attrtext.endswith('/') or source[end-2:end] == '/>'
        # parse attributes
        attrib = {}
        for am in _ATTR_RE.finditer(attrtext):
            aname = am.group(1)
            av = am.group(2)
            if (av.startswith('"') and av.endswith('"')) or (av.startswith("'") and av.endswith("'")):
                av = av[1:-1]
            attrib[aname] = av
        pos = end
        if closing:
            # pop until matching open
            if len(stack) == 1:
                continue
            for i in range(len(stack)-1, 0, -1):
                if stack[i].tag.lower() == tagname.lower():
                    while len(stack)-1 >= i:
                        stack.pop()
                    break
            else:
                continue
        else:
            node = TSNode(tagname, attrib, '')
            stack[-1].children.append(node)
            if not self_close:
                stack.append(node)

    _coalesce_text(root)
    return root

def _coalesce_text(node: TSNode):
    # merge adjacent text nodes and clean small whitespace-only nodes
    if not node.children:
        return
    new_children = []
    buf = []
    for ch in node.children:
        if ch.tag == '#text':
            buf.append(ch.text)
        else:
            if buf:
                t = ''.join(buf)
                if t != '':
                    new_children.append(TSNode('#text', {}, t))
                buf = []
            new_children.append(ch)
    if buf:
        t = ''.join(buf)
        if t != '':
            new_children.append(TSNode('#text', {}, t))
    node.children = new_children
    for ch in node.children:
        if ch.tag != '#text':
            _coalesce_text(ch)

# -----------------------------
# TagScript Interpreter
# -----------------------------
class TagScriptRuntimeError(Exception):
    pass

class _ReturnSignal:
    def __init__(self, value):
        self.value = value

class TagScriptInterpreter:
    def __init__(self, input_fn=None, output_fn=None, stdlib_path='stdlib'):
        self.env = {}
        self.consts = {}
        self.functions = {}
        self.modules = {}
        self.input_fn = input_fn or (lambda prompt=None: input(prompt or '> '))
        self.output_fn = output_fn or print
        self.stop_requested = False
        self.last_exception = None
        self.stdlib_path = stdlib_path
        # extras like math/time
        self.extra_names = {}
        try:
            import math, time
            self.extra_names['math'] = math
            self.extra_names['time'] = time
        except Exception:
            pass

    def reset(self):
        self.env.clear()
        self.consts.clear()
        self.functions.clear()
        self.modules.clear()
        self.stop_requested = False
        self.last_exception = None

    def load_stdlib(self, name):
        try:
            specname = f"stdlib.{name}"
            mod = importlib.import_module(specname)
            if hasattr(mod, 'module'):
                self.modules[name] = mod.module
                return mod.module
            else:
                d = {k: getattr(mod, k) for k in dir(mod) if not k.startswith('_')}
                self.modules[name] = d
                return d
        except ModuleNotFoundError:
            path = os.path.join(self.stdlib_path, f"{name}.py")
            if os.path.exists(path):
                spec = importlib.util.spec_from_file_location(specname, path)
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                if hasattr(mod, 'module'):
                    self.modules[name] = mod.module
                    return mod.module
            raise

    # parse uses forgiving parser
    def parse(self, source):
        try:
            root = parse_tagscript(source)
            return root
        except Exception as e:
            raise TagScriptRuntimeError(f"Parse error: {e}")

    def _interp_text(self, text):
        if text is None:
            return ''
        res = str(text)
        # handle {{ expr }} interpolation
        def repl(m):
            expr = m.group(1).strip()
            try:
                ev = SafeEvaluator(env=self.env, extras=self.extra_names)
                val = ev.eval(expr)
                return str(val)
            except Exception:
                return '{{' + expr + '}}'
        res = re.sub(r'\{\{\s*(.*?)\s*\}\}', repl, res)
        # fallback {var}
        for k, v in list(self.env.items()):
            try:
                res = res.replace(f"{{{k}}}", str(v))
            except Exception:
                pass
        return res

    def _eval_attr(self, attr_value):
        if attr_value is None:
            return None
        s = str(attr_value).strip()
        if (s.startswith('"') and s.endswith('"')) or (s.startswith("'") and s.endswith("'")):
            inner = s[1:-1]
            return self._interp_text(inner)
        ev = SafeEvaluator(env=self.env, extras=self.extra_names)
        return ev.eval(s)

    def run(self, root: TSNode):
        node = root
        if root.tag.lower() == 'root':
            # find page
            page = None
            for ch in root.children:
                if ch.tag.lower() == 'page':
                    page = ch
                    break
            node = page or root
            # find start inside page
            for ch in node.children:
                if ch.tag.lower() == 'start':
                    node = ch
                    break
        return self._exec_block(node)

    def _exec_block(self, node: TSNode):
        result = None
        for child in list(node.children):
            if self.stop_requested:
                break
            if child.tag == '#text':
                if child.text.strip():
                    self.output_fn(self._interp_text(child.text))
                continue
            result = self._exec_node(child)
            if isinstance(result, _ReturnSignal):
                return result
        return result

    def _exec_node(self, node: TSNode):
        tag = node.tag.lower()

        if tag == 'write':
            txt = ''
            if node.children and node.children[0].tag == '#text':
                txt = node.children[0].text
            else:
                txt = node.text
            self.output_fn(self._interp_text(txt))
            return None

        if tag == 'take':
            prompt = node.attrib.get('prompt') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            val = self.input_fn(self._interp_text(prompt or ''))
            return val

        if tag == 'letssay':
            name = node.attrib.get('name')
            if not name:
                content = ''
                if node.children and node.children[0].tag == '#text':
                    content = node.children[0].text.strip()
                elif node.text:
                    content = node.text.strip()
                if '=' in content:
                    lhs, rhs = content.split('=', 1)
                    name = lhs.strip()
                    val = self._eval_attr(rhs.strip())
                    self.env[name] = val
                    return None
                raise TagScriptRuntimeError('letssay missing name')
            if 'value' in node.attrib:
                val = self._eval_attr(node.attrib['value'])
            elif node.children and node.children[0].tag == 'take':
                val = self._exec_node(node.children[0])
            elif node.children and node.children[0].tag == '#text':
                val = self._interp_text(node.children[0].text)
            else:
                val = None
            self.env[name] = val
            return None

        if tag == 'fixed':
            name = node.attrib.get('name')
            if not name:
                raise TagScriptRuntimeError('fixed requires name attribute')
            if 'value' in node.attrib:
                val = self._eval_attr(node.attrib['value'])
            elif node.children and node.children[0].tag == '#text':
                val = self._interp_text(node.children[0].text)
            else:
                val = None
            self.consts[name] = val
            self.env[name] = val
            return None

        if tag == 'isnow':
            name = node.attrib.get('name')
            if not name:
                content = ''
                if node.children and node.children[0].tag == '#text':
                    content = node.children[0].text.strip()
                elif node.text:
                    content = node.text.strip()
                if '=' in content:
                    lhs, rhs = content.split('=', 1)
                    name = lhs.strip()
                    val = self._eval_attr(rhs.strip())
                else:
                    raise TagScriptRuntimeError('isnow bad assignment')
            else:
                val = self._eval_attr(node.attrib['value']) if 'value' in node.attrib else None
            if name in self.consts:
                raise TagScriptRuntimeError('Cannot reassign fixed constant')
            self.env[name] = val
            return None

        if tag in ('whentrue', 'if'):
            cond = node.attrib.get('value') or node.attrib.get('condition') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            try:
                ok = bool(ev.eval(cond))
            except Exception as e:
                raise TagScriptRuntimeError(f'Condition eval error: {e}')
            if ok:
                return self._exec_block(node)
            return None

        if tag in ('whentruealso', 'elif'):
            cond = node.attrib.get('value') or node.attrib.get('condition') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            try:
                ok = bool(ev.eval(cond))
            except Exception as e:
                raise TagScriptRuntimeError(f'Condition eval error: {e}')
            if ok:
                return self._exec_block(node)
            return None

        if tag in ('otherwise', 'else'):
            return self._exec_block(node)

        if tag in ('aslong', 'while'):
            cond = node.attrib.get('value') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            guard = 0
            while True:
                if self.stop_requested:
                    break
                try:
                    ok = bool(ev.eval(cond))
                except Exception as e:
                    raise TagScriptRuntimeError(f'While condition eval error: {e}')
                if not ok:
                    break
                res = self._exec_block(node)
                if isinstance(res, _ReturnSignal):
                    return res
                guard += 1
                if guard > 200000:
                    raise TagScriptRuntimeError('Loop guard exceeded (possible infinite loop)')
            return None

        if tag in ('foreach', 'for'):
            item_name = node.attrib.get('item', 'item')
            iterable = node.attrib.get('in') or node.attrib.get('inlist') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            ev = SafeEvaluator(env=self.env, extras=self.extra_names)
            it = ev.eval(iterable)
            if hasattr(it, '__iter__'):
                for val in it:
                    if self.stop_requested:
                        break
                    self.env[item_name] = val
                    res = self._exec_block(node)
                    if isinstance(res, _ReturnSignal):
                        return res
                return None
            raise TagScriptRuntimeError('foreach: object not iterable')

        if tag == 'additem':
            lstname = node.attrib.get('list')
            item = node.attrib.get('item')
            if lstname is None:
                raise TagScriptRuntimeError('additem missing list attr')
            val = self._eval_attr(item)
            lst = self.env.get(lstname)
            if lst is None:
                lst = []
                self.env[lstname] = lst
            lst.append(val)
            return None

        if tag == 'put':
            mapname = node.attrib.get('map') or node.attrib.get('dict')
            key = node.attrib.get('key')
            val_attr = node.attrib.get('value')
            val = self._eval_attr(val_attr)
            mp = self.env.get(mapname)
            if mp is None:
                mp = {}
                self.env[mapname] = mp
            mp[self._eval_attr(key)] = val
            return None

        if tag == 'getfrom':
            mapname = node.attrib.get('map') or node.attrib.get('dict')
            key = node.attrib.get('key')
            default = node.attrib.get('default')
            mp = self.env.get(mapname, {})
            return mp.get(self._eval_attr(key), self._eval_attr(default))

        if tag == 'doit':
            name = node.attrib.get('name')
            args = node.attrib.get('args', '')
            args = [a.strip() for a in args.split(',') if a.strip()] if args else []
            self.functions[name] = (node, args)
            return None

        if tag == 'useit':
            callname = node.attrib.get('call') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            with_arg = node.attrib.get('with')
            args = []
            if with_arg:
                parts = [p.strip() for p in with_arg.split(',') if p.strip()]
                ev = SafeEvaluator(env=self.env, extras=self.extra_names)
                for p in parts:
                    args.append(ev.eval(p))
            if callname and '.' in callname:
                modname, fname = callname.split('.', 1)
                mod = self.modules.get(modname) or self.load_stdlib(modname)
                fn = mod.get(fname)
                if fn is None:
                    raise TagScriptRuntimeError(f'Module function not found: {fname}')
                return fn(*args)
            if callname in self.functions:
                fn_node, fn_args = self.functions[callname]
                backup = dict(self.env)
                try:
                    for i, a in enumerate(fn_args):
                        self.env[a] = args[i] if i < len(args) else None
                    res = self._exec_block(fn_node)
                    if isinstance(res, _ReturnSignal):
                        return res.value
                finally:
                    self.env = backup
                return None
            fn = self.env.get(callname)
            if callable(fn):
                return fn(*args)
            raise TagScriptRuntimeError(f'Function not found: {callname}')

        if tag == 'giveback':
            if 'value' in node.attrib:
                v = self._eval_attr(node.attrib.get('value'))
            elif node.children and node.children[0].tag == '#text':
                v = self._interp_text(node.children[0].text)
            else:
                v = None
            return _ReturnSignal(v)

        if tag == 'maybework':
            try:
                return self._exec_block(node)
            except Exception as e:
                self.last_exception = e
                return None

        if tag == 'ifbroken':
            name = node.attrib.get('as') or 'err'
            if self.last_exception is not None:
                self.env[name] = self.last_exception
                return self._exec_block(node)
            return None

        if tag == 'breakit':
            msg = node.attrib.get('value') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or 'Error')
            raise TagScriptRuntimeError(msg)

        if tag == 'fileopen':
            path = node.attrib.get('path')
            mode = node.attrib.get('mode', 'r')
            save = node.attrib.get('save')
            f = open(path, mode, encoding='utf-8')
            if save:
                self.env[save] = f
            return f

        if tag == 'fileread':
            fref = node.attrib.get('file')
            save = node.attrib.get('save')
            f = self.env.get(fref) if fref else None
            if f is None and fref:
                f = open(fref, 'r', encoding='utf-8')
            content = f.read() if f else ''
            if save:
                self.env[save] = content
            return content

        if tag == 'filewrite':
            fref = node.attrib.get('file')
            text = node.attrib.get('text') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text or '')
            f = self.env.get(fref)
            if callable(f):
                f(text)
            elif hasattr(f, 'write'):
                f.write(str(text))
            else:
                with open(fref, 'w', encoding='utf-8') as fh:
                    fh.write(str(text))
            return None

        if tag == 'fileclose':
            fref = node.attrib.get('file')
            f = self.env.get(fref)
            if hasattr(f, 'close'):
                f.close()
            return None

        if tag == 'bring':
            modname = node.attrib.get('module') or node.attrib.get('name') or (node.children[0].text if node.children and node.children[0].tag == '#text' else node.text)
            if modname is None:
                raise TagScriptRuntimeError('bring missing module name')
            modname = str(modname).strip()
            try:
                m = self.load_stdlib(modname)
                return m
            except Exception as e:
                raise TagScriptRuntimeError(f'Error loading module {modname}: {e}')

        # unknown/wrapper tags: execute children
        return self._exec_block(node)

# -----------------------------
# Simple Tkinter IDE
# -----------------------------
class TagScriptIDE(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title('TagScript IDE')
        self.geometry('1000x700')
        self.protocol('WM_DELETE_WINDOW', self._on_close)

        # output queue and run state to avoid UI freeze
        self.output_queue = queue.Queue()
        self.running = False

        self._make_widgets()

        # interpreter and thread control
        # output_fn will put text into run_queue via _ide_output
        self.run_queue = queue.Queue()
        self.interpreter = TagScriptInterpreter(input_fn=self._prompt_input, output_fn=self._ide_output)
        self.run_thread = None
        self.current_file = None
        self._setup_keybindings()

        # pump output queues
        self.after(50, self.process_output)
        self.after(100, self._pump_queue)

    def _make_widgets(self):
        toolbar = tk.Frame(self)
        toolbar.pack(side='top', fill='x')
        btn_open = tk.Button(toolbar, text='Open', command=self.open_file)
        btn_open.pack(side='left')
        btn_save = tk.Button(toolbar, text='Save', command=self.save_file)
        btn_save.pack(side='left')
        btn_run = tk.Button(toolbar, text='Run', command=self.run_script)
        btn_run.pack(side='left')
        btn_stop = tk.Button(toolbar, text='Stop', command=self.stop_script)
        btn_stop.pack(side='left')

        paned = ttk.Panedwindow(self, orient='horizontal')
        paned.pack(fill='both', expand=True)

        editor_frame = tk.Frame(paned)
        paned.add(editor_frame, weight=3)
        self.editor = tk.Text(editor_frame, wrap='none', undo=True)
        self.editor.pack(fill='both', expand=True)

        right_frame = tk.Frame(paned, width=300)
        paned.add(right_frame, weight=1)

        console_label = tk.Label(right_frame, text='Console')
        console_label.pack()
        self.console = tk.Text(right_frame, height=15, bg='black', fg='white')
        self.console.pack(fill='both', expand=True)

        vars_label = tk.Label(right_frame, text='Variables')
        vars_label.pack()
        self.vars_box = tk.Text(right_frame, height=10)
        self.vars_box.pack(fill='both', expand=True)

    def _setup_keybindings(self):
        self.bind_all('<Control-s>', lambda e: self.save_file())
        self.bind_all('<Control-o>', lambda e: self.open_file())
        self.bind_all('<Control-r>', lambda e: self.run_script())

    # File operations
    def open_file(self):
        path = filedialog.askopenfilename(filetypes=[('TagScript', '*.ts'), ('All', '*.*')])
        if not path:
            return
        with open(path, 'r', encoding='utf-8') as f:
            src = f.read()
        self.editor.delete('1.0', 'end')
        self.editor.insert('1.0', src)
        self.current_file = path
        self.title(f'TagScript IDE - {os.path.basename(path)}')

    def save_file(self):
        path = self.current_file or filedialog.asksaveasfilename(defaultextension='.ts', filetypes=[('TagScript', '*.ts'), ('All', '*.*')])
        if not path:
            return
        with open(path, 'w', encoding='utf-8') as f:
            f.write(self.editor.get('1.0', 'end'))
        self.current_file = path
        self.title(f'TagScript IDE - {os.path.basename(path)}')

    # I/O adapters for interpreter
    def _prompt_input(self, prompt=None):
        return simpledialog.askstring('Input', prompt or 'Input:')

    def _ide_output(self, text):
        # called by interpreter from worker thread; enqueue for UI
        self.run_queue.put(('out', str(text)))

    def _update_vars_view(self):
        self.vars_box.delete('1.0', 'end')
        try:
            items = list(self.interpreter.env.items())
            for k, v in items:
                self.vars_box.insert('end', f"{k} = {repr(v)}\n")
        except Exception:
            pass

    def run_script(self):
        if self.run_thread and self.run_thread.is_alive():
            messagebox.showinfo('TagScript IDE', 'Script already running')
            return
        src = self.editor.get('1.0', 'end')
        # clear console
        self.console.delete('1.0', 'end')
        self.interpreter.reset()

        def worker():
            try:
                root = self.interpreter.parse(src)
            except Exception as e:
                self.run_queue.put(('err', f'Parse error: {e}'))
                return
            try:
                self.interpreter.run(root)
                self.run_queue.put(('done', 'Execution finished'))
            except Exception as e:
                self.run_queue.put(('err', f'Runtime error: {e}'))
            finally:
                self.run_queue.put(('vars', None))

        self.run_thread = threading.Thread(target=worker, daemon=True)
        self.run_thread.start()

    def stop_script(self):
        if self.run_thread and self.run_thread.is_alive():
            self.interpreter.stop_requested = True
            self.run_queue.put(('out', 'Stop requested'))
        else:
            self.run_queue.put(('out', 'No running script'))

    def _pump_queue(self):
        try:
            while True:
                typ, payload = self.run_queue.get_nowait()
                if typ == 'out':
                    self.console.insert('end', payload + '\n')
                    self.console.see('end')
                elif typ == 'err':
                    self.console.insert('end', '[ERROR] ' + payload + '\n')
                    self.console.see('end')
                elif typ == 'done':
                    self.console.insert('end', payload + '\n')
                elif typ == 'vars':
                    self._update_vars_view()
        except queue.Empty:
            pass
        # call again
        self.after(100, self._pump_queue)

    def process_output(self):
        # kept for backward compatibility / future use
        # currently _pump_queue handles interpreter output
        self.after(200, self.process_output)

    def _on_close(self):
        if messagebox.askokcancel('Quit', 'Exit TagScript IDE?'):
            self.destroy()

# -----------------------------
# Entry point
# -----------------------------
def main():
    app = TagScriptIDE()
    sample = '''<page>
    <start>
        <write>Welcome to TagScript!</write>
        <letssay name="name" value="'World'"/>
        <write>Hello {{ name }}</write>

        <!-- example loop -->
        <letssay name="i" value="0"/>
        <aslong value="i < 3">
            <write>Loop {{ i }}</write>
            <isnow name="i" value="i + 1"/>
        </aslong>
    </start>
</page>
'''
    app.editor.insert('1.0', sample)
    app.mainloop()

if __name__ == '__main__':
    main()
