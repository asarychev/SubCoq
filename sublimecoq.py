import re, os.path
import sublime, sublime_plugin
from .coqtop import Coqtop, find_coqtop

class CoqtopManager:
    coqtop_view = None

    def __init__(self):
        self.coqtop = None
        self.ready = False
        self.output_width = 78
        self.sentence_no = 0
        self.last_output = ""
        self.expect_success = False
        self.retry_on_empty = None
        self.ignore_replies = 0
        self.theorem = None

        self.redirect_view = None
        self.editor_view = None
        self.autorun_point = None
        self.autorun_forward = True
        self.autorun_enabled = False

        self.debug = False
        self.position = 0
        self.stack = []
        self.scope = 'toplevel'

        self.settings = sublime.load_settings('Sublime-Coq.sublime-settings')
        self.settings.add_on_change('coq_debug', self._update_debug)
        self._update_debug()

    def _update_debug(self):
        flags = self.settings.get('coq_debug')

        self.debug = 'manager' in flags
        if self.coqtop is not None:
            self.coqtop.debug = 'coqtop' in flags

    def start(self):
        path = self.settings.get('coqtop_path') or find_coqtop()
        if path is None:
            sublime.error_message('Cannot find Coqtop.')
            return False
        pwd = os.path.dirname(sublime.active_window().active_view().file_name())
        args = ["-R", pwd, ""]
        args = self.settings.get('coqtop_args') + args
        debug = 'coqtop' in self.settings.get('coq_debug')

        self.coqtop = Coqtop(self, path, args, debug)
        return True

    def stop(self):
        if self.coqtop is not None:
            self.ready = False
            self.coqtop.kill()

    def send(self, statement, expect_success=False, retry_on_empty=None,
             redirect_view=None, need_output_width=None):
        self.ready = False

        if self.redirect_view != redirect_view:
            self.redirect_view = redirect_view

        if need_output_width is not None and self.output_width != need_output_width:
            self.output_width = need_output_width
            self.ignore_replies = 1
            statement = 'Set Printing Width {:d}. {}'\
                        .format(self.output_width, statement)

        output_view = self.redirect_view or self.coqtop_view
        sentence_no = self.sentence_no
        def show_progress():
            if not self.ready and self.sentence_no == sentence_no:
                output_view.run_command('coq_output', {'output': 'Running...'})
        sublime.set_timeout_async(show_progress, 100)

        self.expect_success = expect_success
        self.retry_on_empty = retry_on_empty
        self.coqtop.send(statement)

    def receive(self, output, prompt):
        self.ready = True
        self.sentence_no += 1

        output = output.strip()
        if not output:
            if self.ignore_replies > 0:
                self.ignore_replies -= 1
                return

            if self.retry_on_empty:
                self.send(self.retry_on_empty, redirect_view=self.redirect_view)
            else:
                output = self.last_output

        # Clean up some useless messages
        output = re.sub(r'''
            \AToplevel\ input,.+\n
        |   \ \(ID\ \d+\)
        |   \(dependent\ evars:\ \(printing\ disabled\)\ \)
        ''', '', output, flags=re.X)

        output_view = self.redirect_view or self.coqtop_view
        output_view.run_command('coq_output', {'output': output})
        if self.redirect_view:
            return

        self.theorem = re.sub(r'.*\|(.*)\|.*', r'\1', prompt)
        if self.expect_success:
            self.expect_success = False
            if re.search(r'^(Error:|Syntax [Ee]rror:)', output, re.M) is None:
                self.editor_view.run_command('coq_success', {'prompt': prompt})
            else:
                self.autorun_enabled = False
                return

        self.last_output = output

    def _ident(self, kind, position):
        return "coq-{}".format(position)

    def empty(self):
        return len(self.stack) == 0

    def push(self, kind, region, new_scope, defined=[]):
        if self.debug:
            print('coq: advance through {} at {} ({}), define {}'
                  .format(kind, region, new_scope, defined))
        self.stack.append((kind, self.position, self.scope, defined))
        self.position, old_position = region.end(), self.position
        self.scope = new_scope

        ident = self._ident(kind, old_position)
        return ident

    def pop(self):
        old_scope = self.scope
        kind, self.position, self.scope, defined = self.stack.pop()
        if self.debug:
            print('coq: undo to {} at {} ({}), undefine {}'
                  .format(kind, self.position, self.scope, defined))

        ident = self._ident(kind, self.position)
        return kind, ident, old_scope, defined

    def rev_find(self, need_scope):
        found = False
        for _kind, position, scope, _defined in self.stack[::-1]:
            if found:
                return position
            if scope == need_scope:
                found = True

managers = {}

# Starting/stopping coqtop

def _get_view_width(view):
    return int(view.viewport_extent()[0] / view.em_width()) - 1

class ManagerCommand(sublime_plugin.TextCommand):
    def is_enabled(self):
        manager = self._manager()
        return manager is not None and manager.ready

    def _manager(self):
        buffer_id = self.view.buffer_id()
        if buffer_id in managers:
            return managers[buffer_id]

class CoqStartCommand(ManagerCommand):
    def is_enabled(self):
        return (self.view.settings().get('syntax').endswith('/Coq.sublime-syntax') and
                self._manager() is None)

    def run(self, edit):
        manager = self._manager()
        if manager and manager.coqtop is not None:
            self.view.run_command('coq_stop')

        manager = managers[self.view.buffer_id()] = CoqtopManager()

        window = self.view.window()
        if manager.coqtop_view is None:
            if window.num_groups() == 1:
                window.run_command('new_pane', {'move': False})

            coqtop_group = window.num_groups() - 1
            coqtop_view = window.active_view_in_group(coqtop_group)
            coqtop_view.set_syntax_file('Packages/Sublime-Coq/Coq Toplevel.sublime-syntax')
            coqtop_view.set_name('*COQTOP*')
            coqtop_view.set_read_only(True)
            coqtop_view.set_scratch(True)
            coqtop_view.settings().set('gutter', False)
            coqtop_view.settings().set('line_numbers', False)
            coqtop_view.settings().set('word_wrap', True)
            coqtop_view.settings().set('wrap_width', 0)
            coqtop_view.settings().set('scroll_past_end', False)
            coqtop_view.settings().set('draw_indent_guides', False)
            coqtop_view.settings().set('draw_centered', False)
            coqtop_view.settings().set('coq', 'output')
            CoqtopManager.coqtop_view = coqtop_view

        manager.editor_view = self.view
        if manager.start():
            manager.editor_view.settings().set('coq', 'editor')
        else:
            manager.editor_view.settings().set('coq', None)
        window.focus_view(manager.editor_view)

class CoqRestartCommand(CoqStartCommand):
    def is_enabled(self):
        return self._manager() is not None

class CoqStopCommand(ManagerCommand):
    def run(self, edit):
        manager = self._manager()

        manager.coqtop_view.run_command('coq_output', {'output': 'Coq has been stopped.'})

        while not manager.empty():
            _kind, region_name, _scope, _defined = manager.pop()
            manager.editor_view.erase_regions(region_name)
        manager.editor_view.settings().set('coq', None)

        manager.stop()
        del managers[self.view.buffer_id()]

def plugin_unloaded():
    for manager in list(managers.values()):
        manager.settings.clear_on_change('coq_debug')
        manager.editor_view.run_command('coq_stop')

# Managing the coqtop window

class CoqOutputCommand(sublime_plugin.TextCommand):
    def run(self, edit, output=""):
        was_empty = (self.view.size() == 0)
        self.view.set_read_only(False)
        self.view.replace(edit, sublime.Region(0, self.view.size()), output)
        self.view.set_read_only(True)
        if was_empty:
            # Or the entire contents of a view is selected.
            self.view.sel().clear()

        goal = self.view.find_by_selector('meta.goal.coq')
        if goal:
            _, ty = self.view.text_to_layout(goal[0].end())
            _, h = self.view.viewport_extent()
            self.view.set_viewport_position((0, ty - h/2), animate=False)

# Advancing through the proof

RE_COMMENT    = r'\(\*(.|\n)*?\*\)'
RE_STATEMENT  = r'[*+-]+|(.|\n)*?[^\.]\.(?=\s|$)'
RE_DEFINITION = r'\s*[A-Z][a-z]+'

class CoqCommand(ManagerCommand):
    def _find_at_pos(self, re, position=None):
        manager = self._manager()
        if position is None:
            position = manager.position
        position = manager.editor_view.find(r'\s*', position).end()
        return manager.editor_view.find(re, position)

    def _substr_find_at_pos(self, re, position=None):
        manager = self._manager()
        region = self._find_at_pos(re, position)
        if region:
            return manager.editor_view.substr(region)

    def _find_statement(self):
        manager = self._manager()
        region = self._find_at_pos(RE_STATEMENT)
        while manager.editor_view.match_selector(region.end(), 'comment'):
            next_region = self._find_at_pos(RE_STATEMENT, region.end())
            if not next_region:
                return
            region = sublime.Region(region.begin(), next_region.end())
        return region

    def _focus_point(self, point):
        manager = self._manager()
        region = sublime.Region(point, point)
        manager.editor_view.sel().clear()
        manager.editor_view.sel().add(region)
        manager.editor_view.show(region)

    def _add_region(self, region_name, region):
        manager = self._manager()
        manager.editor_view.add_regions(region_name, [region], 'meta.proven.coq')
        whitespace = manager.editor_view.find(r'(?=\S)| \n\s+(?=\n)|\s(?=\n)', region.end())
        self._focus_point(max(whitespace.end(), region.end() + 1))

    def _erase_region(self, region_name):
        manager = self._manager()
        region = manager.editor_view.get_regions(region_name)[0]
        manager.editor_view.erase_regions(region_name)
        self._focus_point(region.begin())
        return region

    def _autorun(self):
        manager = self._manager()
        if manager.autorun_enabled:
            if manager.debug:
                print('coq: running {} until {} (now {})'
                      .format("forward" if manager.autorun_forward else "backward",
                              manager.autorun_point, manager.position))
            if manager.autorun_forward and manager.position < manager.autorun_point:
                manager.editor_view.run_command('coq_next_statement')
            elif not manager.autorun_forward and manager.position > manager.autorun_point:
                manager.editor_view.run_command('coq_undo_statement')
            else:
                manager.autorun_enabled = False
                manager.autorun_point = None

class CoqNextStatementCommand(CoqCommand):
    def run(self, edit, until=None):
        manager = self._manager()

        comment_region   = self._find_at_pos(RE_COMMENT)
        statement_region = self._find_statement()
        regions = filter(lambda x: x, [comment_region, statement_region])
        if not regions:
            return
        region = min(regions, key=lambda x: x.begin())

        if region == comment_region:
            region_name = manager.push('comment', region, manager.scope)
            self._add_region(region_name, region)
            self._autorun()
        elif region == statement_region:
            statement = manager.editor_view.substr(region)
            manager.send(statement,
                         expect_success=True,
                         need_output_width=_get_view_width(manager.coqtop_view))

class CoqGoHereCommand(CoqNextStatementCommand):
    def is_enabled(self):
        return super().is_enabled() and self.view.settings().get('coq') == 'editor'

    def run(self, edit):
        manager = self._manager()

        cursor_at = self.view.sel()[0].begin()
        if (manager.autorun_point is None or
                manager.autorun_forward and cursor_at < manager.autorun_point or
                not manager.autorun_forward and cursor_at > manager.autorun_point):
            manager.autorun_point = cursor_at
            manager.autorun_forward = manager.autorun_point > manager.position
            if manager.debug:
                print('coq: run {} until {}'
                      .format("forward" if manager.autorun_forward else "backward",
                              manager.autorun_point))

        manager.autorun_enabled = True
        self._autorun()

class CoqSuccessCommand(CoqCommand):
    def run(self, edit, prompt):
        manager = self._manager()

        defined = list(map(manager.coqtop_view.substr,
                           manager.coqtop_view.find_by_selector('meta.defined.coq')))

        scope = manager.scope
        if manager.theorem:
            if scope == 'toplevel':
                defined.append(manager.theorem)
                scope = 'theorem'
            elif scope == 'theorem':
                if manager.debug:
                    print('coq: started proof')
                scope = 'tactic'

        region = self._find_statement()
        match = re.match(r'\s*([A-Z][a-z]+)', manager.editor_view.substr(region))
        if match:
            keyword = match.group(0)
        else:
            keyword = ""

        if keyword in ['Show', 'Print', 'Check']:
            kind = 'comment'
        elif keyword in ['Qed', 'Admitted', 'Save', 'Defined']:
            kind = 'qed'
            scope = 'toplevel'
        else:
            kind = 'statement'

        if defined and manager.debug:
            print('coq: defined ' + ', '.join(defined))

        region_name = manager.push(kind, region, scope, defined)
        self._add_region(region_name, region)

        sublime.set_timeout_async(lambda: self._autorun())

class CoqClearErrorCommand(CoqCommand):
    def run(self, edit):
        manager = self._manager()

        manager.coqtop_view.run_command('coq_output', {'output': manager.last_output})

class CoqUndoStatementCommand(CoqCommand):
    def is_enabled(self):
        return super().is_enabled() and not self._manager().empty()

    def run(self, edit):
        manager = self._manager()

        if self._undo_one() == 'qed':
            while manager.scope == 'tactic':
                _kind, region_name, _scope, _defined = manager.pop()
                self._erase_region(region_name)

            self._undo_one()

        sublime.set_timeout_async(lambda: self._autorun())

    def _undo_one(self):
        manager = self._manager()

        kind, region_name, scope, defined = manager.pop()
        region = self._erase_region(region_name)

        if kind == 'statement':
            if scope == 'tactic':
                manager.send('Undo.')
            elif manager.theorem and scope == 'theorem':
                manager.send('Abort.')
            elif any(defined):
                for theorem in defined:
                    manager.send('Reset {}.'.format(theorem))
        elif kind == 'comment':
            manager.coqtop_view.run_command('coq_output')

        return kind

class CoqAbortProofCommand(CoqCommand):
    def is_enabled(self):
        manager = self._manager()
        return super().is_enabled() and not manager.empty() and manager.scope == 'tactic'

    def run(self, edit):
        manager = self._manager()

        manager.send('Abort.')
        while manager.scope in ['tactic', 'theorem']:
            _kind, region_name, _scope, _defined = manager.pop()
            self._erase_region(region_name)

# Search

class CoqPanelCommand(CoqCommand):
    def _create_panel(self, name, syntax='Toplevel'):
        full_name = 'Coq {}'.format(name)
        window = self.view.window()
        panel = window.create_output_panel(full_name)
        panel.set_syntax_file('Packages/Sublime-Coq/Coq {}.sublime-syntax'.format(syntax))
        panel.set_read_only(True)
        panel.settings().set('is_widget', True)
        panel.settings().set('word_wrap', True)
        panel.settings().set('wrap_width', 0)
        panel.settings().set('scroll_past_end', False)
        panel.settings().set('rulers', [])
        window.run_command('show_panel', {'panel': 'output.' + full_name})
        return panel

    def _hide_panel(self, name='Coq'):
        full_name = 'Coq {}'.format(name)
        window = self.view.window()
        window.run_command('hide_panel', {'panel': 'output.' + full_name})

class CoqSearchCommand(CoqPanelCommand):
    def input(self, args):
        panel  = self._create_panel('Search', syntax='Search')
        hide = lambda: self._hide_panel('Search')
        return CoqSearchQueryInputHandler(panel, hide, self._manager(),
                                          args['kind'], args.get('quote', None))

    def run(self, edit, kind, coq_search_query=None, coq_search_result=None):
        if coq_search_result:
            manager = self._manager()
            for region in manager.editor_view.sel():
                manager.editor_view.replace(edit, region, coq_search_result)

class CoqSearchQueryInputHandler(sublime_plugin.TextInputHandler):
    def __init__(self, panel, hide, manager, kind, quote):
        self.panel   = panel
        self.hide    = hide
        self.manager = manager
        self.kind    = kind
        self.quote   = quote

    def preview(self, value):
        if value:
            kwargs = {
                'redirect_view': self.panel,
                'need_output_width': _get_view_width(self.panel)
            }

            if self.quote == '"':
                # Not sure what's the best way to indicate invalid input here--
                # let's just sanitize.
                value = re.sub(re.escape(self.quote), '', value)
                self.manager.send('{} "{}".'.format(self.kind, value), **kwargs)
            else:
                # Not sure what's the best way to indicate invalid input here--
                # let's just sanitize.
                value = re.sub(r'\.($|\s+.*)', '', value)
                # Coq's Search command returns an empty output if an exact match
                # is found--in that case, print the exact match.
                self.manager.send('{} ({}).'.format(self.kind, value),
                                  retry_on_empty='Print {}.'.format(value),
                                  **kwargs)
        else:
            self.panel.run_command('coq_output', {'output': 'Enter search query.'})

    def validate(self, value):
        return not self.panel.find_by_selector('message.error')

    def next_input(self, args):
        return CoqSearchResultInputHandler(self.panel, self.hide)

class CoqSearchResultInputHandler(sublime_plugin.ListInputHandler):
    def __init__(self, panel, hide):
        self.panel = panel
        self.hide  = hide

    def list_items(self):
        return [self.panel.substr(r) for r in self.panel.find_by_selector('entity.name.coq')]

    def confirm(self, value):
        self.hide()

# Evaluation

class CoqEvaluateCommand(CoqPanelCommand):
    def input(self, args):
        panel  = self._create_panel('Evaluation')
        cancel = lambda: self._hide_panel('Evaluation')
        return CoqEvaluateInputHandler(panel, cancel, self._manager(),
                                       args['kind'])

    def run(self, edit, kind, coq_evaluate=None):
        pass

class CoqEvaluateInputHandler(sublime_plugin.TextInputHandler):
    def __init__(self, panel, cancel, manager, kind):
        self.panel   = panel
        self.cancel  = cancel
        self.manager = manager
        self.kind    = kind

    def preview(self, value):
        if value:
            # Not sure what's the best way to indicate invalid input here--
            # let's just sanitize.
            value = re.sub(r'\.($|\s+.*)', '', value)
            self.manager.send('{} {}.'.format(self.kind, value),
                              redirect_view=self.panel,
                              need_output_width=_get_view_width(self.panel))
        else:
            self.panel.run_command('coq_output', {'output': 'Enter an expression.'})

# Event listener

class CoqContext(sublime_plugin.EventListener):
    def on_query_context(self, view, key, operator, operand, match_all):
        if key == 'coq':
            value = view.settings().get('coq')
        elif key == 'coq_error':
            value = bool(CoqtopManager.coqtop_view.find_by_selector('message.error'))
        else:
            value = None
        if value is not None:
            if operator == sublime.OP_EQUAL:
                return value == operand
            elif operator == sublime.OP_NOT_EQUAL:
                return value != operand
            else:
                return False
        return None

    def _manager(self, view):
        buffer_id = view.buffer_id()
        if buffer_id in managers:
            return managers[buffer_id]

    def on_selection_modified(self, view):
        manager = self._manager(view)
        if manager:
            pos = view.sel()[-1].end()
            view.set_read_only(view.size() > 0 and 0 < pos <= manager.position)

    def on_text_command(self, view, command_name, args):
        manager = self._manager(view)
        if manager:
            # This fixes the annoying issue that if you set the view read-only such
            # that the last region can't be erased with backspace, it can't be appended
            # to either. Only Enter runs a text command though.
            if (view.is_read_only() and view.sel()[0].begin() == manager.position and
                    command_name == 'insert'):
                view.set_read_only(False)

    def _update_output(self, view):
        if (view.settings().get('coq') == 'output' or
                view.settings().get('is_widget') or
                view.is_scratch()):
            return

        manager = self._manager(view)
        if manager:
            output = manager.last_output
        else:
            output = 'Coqtop is not running in the active tab.'
        if CoqtopManager.coqtop_view:
            CoqtopManager.coqtop_view.run_command('coq_output', {'output': output})

    def on_activated(self, view):
        self._update_output(view)

    def on_deactivated(self, view):
        self._update_output(view)

    def on_pre_close(self, view):
        if view.settings().get('coq') == 'output':
            for manager in list(managers.values()):
                manager.editor_view.run_command('coq_stop')
            CoqtopManager.coqtop_view = None
        elif view.settings().get('coq') == 'editor':
            self._manager(view).editor_view.run_command('coq_stop')
