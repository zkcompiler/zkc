"""The retired Common export is not an alternate source authority."""
from cases import case, counted
from commands import Commands
from tools import records

commands = Commands(records())

with case('common-export-command-is-retired'):
    commands.source('protocol-lean', 'module {}', '--symbol=main',
                    refuses='unknown-command')

commands.save()
counted()
