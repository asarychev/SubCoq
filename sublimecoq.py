import re, os.path
import itertools
import subprocess, threading
import queue
import xml.sax.saxutils

import sublime, sublime_plugin
# Event listener

CKEY = 'coq'
RKEY = 'QQkey'

class RegInfo(object):
    def __init__(self, a, b, h):
        self.a = a
        self.b = b
        self.hash = h
        self.state_id = None

    def region(self):
        return sublime.Region(self.a, self.b)

    def __str__(self):
        return str((self.a, self.b))

class State(object):
    def __init__(self, view):
        self.view = view
        self.queue = []
        self.proven = []
        self.coqtop = CoqTop()

    def add_ws(self):
        p0 = p = self._pos()
        lvl = 0
        while True:
            if lvl > 0:
                # Inside a comment.
                r = self.view.find(r'"|\*\)|\(\*', p)
                if not r:
                    # No closing parenthesis
                    return False

                assert p < r.end()
                p = r.end()
                if self.view.substr(p-1) == '"':
                    r = self.view.find(r'"', p)
                    if not r:
                        # No closing quote
                        return False

                    assert p < r.end()
                    p = r.end()
                elif self.view.substr(p-1) == '*':
                    lvl += 1
                else:
                    lvl -= 1
            else:
                # Outside of a comment.
                r = self.view.find(r'\s+', p)
                if r and r.begin() == p:
                    assert p < r.end()
                    p = r.end()

                r = self.view.find(r'\(\*', p)
                if r and r.begin() == p:
                    assert p < r.end()
                    p = r.end()
                    lvl += 1
                else:
                    # Done.
                    if p != p0:
                        # Add a comment.
                        self.add_comment(p)

                    return True

    def get_id(self):
        i = len(self.proven) - 1
        if i >= 0 and self.proven[i].state_id is None:
            i -= 1

        if i < 0:
            return self.coqtop.initial_id
        else:
            return self.proven[i].state_id


    def add_region(self, end):
        ri = self._ri(self._pos(), end)
        r = sublime.Region(ri.a, ri.b)
        self.view.show(r)
        cmd = self.view.substr(r)
        # print("cmd: '%s'" % (cmd,))
        self.coqtop._add(cmd, self.get_id(), len(self.proven))
        res = self.coqtop.results.get()
        print("Add result: %s" % (res,))
        assert res.name == 'value' and res._val == 'good'
        new_id = res.pair.state_id._val
        ri.state_id = new_id
        # print("New state_id: %s" % (new_id,))

        self.proven.append(ri)
        self.view.add_regions(RKEY, [x.region() for x in self.proven], 'meta.proven.coq')

    def add_comment(self, end):
        ri = self._ri(self._pos(), end)
        self.proven.append(ri)
        self.view.add_regions(RKEY, [x.region() for x in self.proven], 'meta.proven.coq')

    def _hash(self, r):
        import hashlib
        s = self.view.substr(r)
        return hashlib.sha256(s.encode("utf-8")).digest()

    def _ri(self, a, b):
        ha = self._hash(sublime.Region(a, b))
        return RegInfo(a, b, ha)

    def _pos(self):
        return self.proven[-1].b if self.proven else 0

    def next(self):
        if self.add_ws():
            p = self._pos()
            r = self.view.find(r'-+|\+=|\*+|{|}', p)
            # print((1, p, r))
            if r and r.begin() == p:
                self.add_region(r.end())
                return True

            r = self.view.find(r'\.', p)
            # print((2, p, r))
            if r:
                self.add_region(r.end())
                return True

        # Couldn't find a new region. Sound?
        # print("No new region!")
        return False

    def detect_changes(self):
        regs = sorted(self.view.get_regions(RKEY))

        for i, (x, r) in enumerate(itertools.zip_longest(self.proven, regs)):
            if x is None or r is None or x.a != r.begin() or x.b != r.end() or (x.hash is not None and  x.hash != self._hash(r)):
                # print("Modified region %d: %s - %s: %s" % (i, x, r))
                del self.proven[i:]
                self.view.add_regions(RKEY, [x.region() for x in self.proven], 'meta.proven.coq')

                s = '<call val="Edit_at"><state_id val="%s"/></call>' % (self.get_id(),)
                self.coqtop._send(s)
                res = self.coqtop.results.get()
                print("Edit_at result: %s" % (res,))

                break

    def goto(self, pos):
        while not (self.proven and pos <= self.proven[-1].b):
            if not self.next():
                # print("Could not get to the cursor.")
                return
        else:
            # print("Already proven at %s" % (pos,))
            return      # It's already proven

_state = {}

class Tag(object):
    def __init__(self, name, attrs):
        self.name = name
        self.a = attrs
        self.children = []

    def __getattr__(self, name):
        if name.startswith('_'):
            return self.a[name[1:]]
        else:
            for t in self.children:
                if isinstance(t, Tag) and t.name == name:
                    return t

            raise AttributeError("No child %s" % (name,))

    # def __str__(self):
    #     return "Tag %s, %s" % (self.name, self.a,)

    def __repr__(self):
        return "Tag %s: %s %s" % (self.name, self.a, self.children)

class CoqTop(object):
    ''
    exe = '/Applications/CoqIDE_8.9.1.app/Contents/Resources/bin/coqidetop'
    # sub = None
    CHUNKSZ = 4096

    def __init__(self):
        cmd = [self.exe, '-main-channel', 'stdfds', '--xml_format=Ppcmds', '-async-proofs', 'on']
        # cmd = ['ls', exe]

        self.sub = subprocess.Popen(cmd, stderr=subprocess.STDOUT, stdout=subprocess.PIPE,
                    stdin =subprocess.PIPE,
                    bufsize=0)

        self.results = queue.Queue()
        self.thr = threading.Thread(target=self.parse_output)
        self.thr.start()

        s = '<call val="About"><unit/></call>'
        self._send(s)
        res = self.results.get()
        print("About result: %s" % (res,))

        s = '<call val="Init"><option val="none"/></call>'
        self._send(s)
        res = self.results.get()
        print("Init result: %s" % (res,))
        assert res.name == 'value' and res._val == 'good'
        state_id = res.state_id._val
        print("Init state_id: %s" % (state_id,))
        self.initial_id = state_id

        # s = '<call val="Status"><bool val="false"/></call>'
        # self._send(s)
        # res = self.results.get()
        # print("Status result: %s" % (res,))

        # s = 'Definition a := 1.'
        # self._add(s, state_id, 0)
        # res = self.results.get()
        # print("Add1 result: %s" % (res,))

        # s = 'Definition b := 1.'
        # self._add(s, 2, 0)
        # res = self.results.get()
        # print("Add2 result: %s" % (res,))

        # s = '<call val="GetOptions"><unit/></call>'
        # self.sub.stdin.write(s.encode('utf-8'))

    def _send(self, s):
        self.sub.stdin.write(s.encode('utf-8'))
        self.sub.stdin.flush()

    def _add(self, cmd, state_id, edit_id):
        s = '<call val="Add"><pair><pair><string>%s</string><int>%s</int></pair><pair><state_id val="%s"/><bool val="true"/></pair></pair></call>' % (xml.sax.saxutils.escape(cmd), edit_id, state_id)
        self._send(s)

    def error(self, msg):
        raise RuntimeError(msg)

    def parse_output(self):
        print("Thread started.")

        self.buf = b''
        self.bpos = 0
        self.tags = [Tag(None, None)]

        while True:

            chunk = self.sub.stdout.read(self.CHUNKSZ)
            if len(chunk) == 0:
                return

            self.buf += chunk
            # print("Got %d chunk" % (len(chunk),))

            while True:
                oldpos = self.bpos
                if self._get_some():
                    assert oldpos < self.bpos
                else:
                    self.buf = self.buf[self.bpos:]
                    self.bpos = 0
                    break   # Read next chunk.

        print("Thread done.")

    def skip_ws(self):
        WS = re.compile(rb'\s*')
        m = WS.match(self.buf, self.bpos)
        self.bpos += len(m.group(0))

    def is_empty(self):
        return self.bpos >= len(self.buf)

    def _get_some(self):
        # get a tag
        self.skip_ws()
        if self.is_empty():
            return False   # Need for more data

        if self.buf[0] != b'<'[0]:
            self.error("Tag expected '%s'" % (self.buf,))

        TAG = re.compile(rb'\s*(.*?)\s*<\s*(.*?)\s*(/?)\s*>')
        m = TAG.match(self.buf, self.bpos)
        if not m:
            return False   # Need for more data

        txt = _e2str(m.group(1))
        if txt:
            self.tags[-1].children.append(txt)
            # print("Txt: %s" % (txt,))

        # Got an openning tag
        s = m.group(2)
        closed = bool(m.group(3))

        # print("Tag: %s %s" % (s, closed,))

        mm = re.match(rb'^(/?)\s*(\S+)\s*', s)
        if mm:
            name = _2str(mm.group(2))
            if mm.group(1):
                # Closing tag
                t = self.tags.pop()
                assert name == t.name, "%s != %s (%s)" % (name, t.name, self.tags)
                self.tags[-1].children.append(t)
                if len(self.tags) == 1:
                    # Got result
                    assert len(self.tags[0].children) == 1
                    res = self.tags[0].children.pop()
                    if res.name == 'feedback':
                       print("Feedback: %s" % (res,))
                    else:
                        self.results.put(res)
            else:
                # Adding tag
                p = pp = len(mm.group(0))
                ATTR = re.compile(rb'''(\S+)\s*=\s*(".*?"|'.*?')\s*''')
                attrs = {}
                for mmm in ATTR.finditer(s, p):
                    assert mmm.start() == pp
                    pp = mmm.end()
                    aname = _2str(mmm.group(1))
                    avalue = _e2str(mmm.group(2))
                    assert aname not in attrs
                    attrs[aname] = avalue[1:-1]

                t = Tag(_2str(mm.group(2)), attrs)
                if closed:
                    self.tags[-1].children.append(t)
                else:
                    self.tags.append(t)

        else:
            self.error("Bad tag: %s" % (s,))

        self.bpos += len(m.group(0))
        return True

    def stop(self):
        if self.sub is not None:
            self.sub.stdin.close()

            res = self.sub.wait()
            print("Popen returned %s" % (res,))
        else:
            print("No sub")

def plugin_loaded():
    '''Clean up'''
    _state.clear()
    for w in sublime.windows():
        for v in w.views():
            v.erase_regions(RKEY)

def plugin_unloaded():
    '''Clean up'''
    for w in sublime.windows():
        for v in w.views():
            v.erase_regions(RKEY)

    for (id, st) in _state.items():
        st.coqtop.stop()

    _state.clear()

def _get_state(view):
    if view.id() not in _state:
        _state[view.id()] = State(view)

    return _state[view.id()]

entities = {
'nbsp': ' ',
'quot': '"',
}
def _e2str(s):
    p = 0
    res = ''
    for m in re.finditer(rb'&(.*?);', s):
        res += s[p:m.start()].decode("utf-8")
        entity = m.group(1).decode("utf-8")
        assert entity in entities, "Unknown entity %s" % (entity,)
        res += entities[entity]
        p = m.end()

    res += s[p:].decode("utf-8")
    return res

def _2str(s):
    return s.decode("utf-8")

class Listener(sublime_plugin.ViewEventListener):
    @classmethod
    def is_applicable(cls, settings):
        return settings.get('syntax').endswith('/Coq.sublime-syntax')

    def on_query_context(self, key, operator, operand, match_all):
        if key != CKEY:
            return None

        return True

        value = self.view.settings().get(CKEY)
        print((self.view.id(), value, key, operator, operand, match_all))

        if value is None:
            return False

        if operator == sublime.OP_EQUAL:
            return value == operand
        if operator == sublime.OP_NOT_EQUAL:
            return value != operand

        return False

    # def on_selection_modified(self):
    #     ''
    #     # print("on_selection_modified in %s" % (self.view.id()))

    def on_modified(self):
        ''

        _get_state(self.view).detect_changes()

    def on_text_command(self, command_name, args):
        ''
        # print("on_text_command %s %s" % (command_name, args))

    def on_close(self):
        print("on_close")
        del _state[self.view.id()]

class CmdBase(sublime_plugin.TextCommand):
    def is_enabled(self):
        return self.view.settings().get('syntax').endswith('/Coq.sublime-syntax')

class CoqNextStatementCommand(CmdBase):
    def run(self, edit, until=None):
        ''
        # print("Next %s" % (edit,))

        _get_state(self.view).next()

class CoqGoHereCommand(CmdBase):
    def run(self, edit, until=None):
        ''
        print("Go here %s" % (edit,))

        sel = self.view.sel()
        if sel:
            cursor_pos = sel[0].begin()
            _get_state(self.view).goto(cursor_pos)
        else:
            print("No selection!")
