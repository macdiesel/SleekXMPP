"""
    SleekXMPP: The Sleek XMPP Library
    Copyright (C) 2010  Nathanael C. Fritz
    This file is part of SleekXMPP.

    See the file LICENSE for copying permission.
"""

from __future__ import absolute_import, unicode_literals

import logging
import base64
import sys
import hashlib
import random
import threading

from sleekxmpp import plugins
from sleekxmpp import stanza
from sleekxmpp.basexmpp import BaseXMPP
from sleekxmpp.stanza import Message, Presence, Iq
from sleekxmpp.xmlstream import XMLStream, RestartStream
from sleekxmpp.xmlstream import StanzaBase, ET
from sleekxmpp.xmlstream.matcher import *
from sleekxmpp.xmlstream.handler import *
from sleekxmpp.xmlstream.tostring.tostring import tostring

# Flag indicating if DNS SRV records are available for use.
SRV_SUPPORT = True
try:
    import dns.resolver
except:
    SRV_SUPPORT = False


log = logging.getLogger(__name__)


class ClientXMPP(BaseXMPP):

    """
    SleekXMPP's client class.

    Use only for good, not for evil.

    Attributes:

    Methods:
        connect          -- Overrides XMLStream.connect.
        del_roster_item  -- Delete a roster item.
        get_roster       -- Retrieve the roster from the server.
        register_feature -- Register a stream feature.
        update_roster    -- Update a roster item.
    """

    def __init__(self, jid, password, ssl=False, plugin_config={},
                 plugin_whitelist=[], escape_quotes=True):
        """
        Create a new SleekXMPP client.

        Arguments:
            jid              -- The JID of the XMPP user account.
            password         -- The password for the XMPP user account.
            ssl              -- Deprecated.
            plugin_config    -- A dictionary of plugin configurations.
            plugin_whitelist -- A list of approved plugins that will be loaded
                                when calling register_plugins.
            escape_quotes    -- Deprecated.
        """
        BaseXMPP.__init__(self, 'jabber:client')

        # To comply with PEP8, method names now use underscores.
        # Deprecated method names are re-mapped for backwards compatibility.
        self.updateRoster = self.update_roster
        self.delRosterItem = self.del_roster_item
        self.getRoster = self.get_roster
        self.registerFeature = self.register_feature

        self.set_jid(jid)
        self.password = password
        self.escape_quotes = escape_quotes
        self.plugin_config = plugin_config
        self.plugin_whitelist = plugin_whitelist
        self.srv_support = SRV_SUPPORT

        self.stream_header = "<stream:stream to='%s' %s %s version='1.0'>" % (
                self.boundjid.host,
                "xmlns:stream='%s'" % self.stream_ns,
                "xmlns='%s'" % self.default_ns)
        self.stream_footer = "</stream:stream>"

        self.features = []
        self.registered_features = []

        #TODO: Use stream state here
        self.authenticated = False
        self.sessionstarted = False
        self.bound = False
        self.bindfail = False
        self.add_event_handler('connected', self.handle_connected)

        self.register_handler(
                Callback('Stream Features',
                         MatchXPath('{%s}features' % self.stream_ns),
                         self._handle_stream_features))
        self.register_handler(
                Callback('Roster Update',
                         MatchXPath('{%s}iq/{%s}query' % (
                             self.default_ns,
                             'jabber:iq:roster')),
                         self._handle_roster))

        #SASL Auth handlers
        sasl_ns = 'urn:ietf:params:xml:ns:xmpp-sasl'
        self.add_handler("<success xmlns='%s' />" % sasl_ns,
                         self._handle_auth_success,
                         name='SASL Sucess',
                         instream=True)
        self.add_handler("<failure xmlns='%s' />" % sasl_ns,
                         self._handle_auth_fail,
                         name='SASL Failure',
                         instream=True)
        self.add_handler("<challenge xmlns='%s' />"  % sasl_ns, 
                         self._handle_sasl_digest_md5_auth, 
                         instream=True)
        
        self.register_feature(
            "<starttls xmlns='urn:ietf:params:xml:ns:xmpp-tls' />",
            self._handle_starttls, True)
        self.register_feature(
            "<mechanisms xmlns='urn:ietf:params:xml:ns:xmpp-sasl' />",
            self._handle_sasl_auth, True)
        self.register_feature(
            "<bind xmlns='urn:ietf:params:xml:ns:xmpp-bind' />",
            self._handle_bind_resource)
        self.register_feature(
            "<session xmlns='urn:ietf:params:xml:ns:xmpp-session' />",
            self._handle_start_session)

    def handle_connected(self, event=None):
        #TODO: Use stream state here
        self.authenticated = False
        self.sessionstarted = False
        self.bound = False
        self.bindfail = False
        self.schedule("session timeout checker", 15,
                      self._session_timeout_check)

    def _session_timeout_check(self):
        if not self.session_started_event.isSet():
            log.debug("Session start has taken more than 15 seconds")
            self.disconnect(reconnect=self.auto_reconnect)

    def connect(self, address=tuple()):
        """
        Connect to the XMPP server.

        When no address is given, a SRV lookup for the server will
        be attempted. If that fails, the server user in the JID
        will be used.

        Arguments:
            address -- A tuple containing the server's host and port.
        """
        self.session_started_event.clear()
        if not address or len(address) < 2:
            if not self.srv_support:
                log.debug("Did not supply (address, port) to connect" + \
                              " to and no SRV support is installed" + \
                              " (http://www.dnspython.org)." + \
                              " Continuing to attempt connection, using" + \
                              " server hostname from JID.")
            else:
                log.debug("Since no address is supplied," + \
                              "attempting SRV lookup.")
                try:
                    xmpp_srv = "_xmpp-client._tcp.%s" % self.server
                    answers = dns.resolver.query(xmpp_srv, dns.rdatatype.SRV)
                except (dns.resolver.NXDOMAIN, dns.resolver.NoAnswer):
                    log.debug("No appropriate SRV record found." + \
                                  " Using JID server name.")
                else:
                    # Pick a random server, weighted by priority.

                    addresses = {}
                    intmax = 0
                    for answer in answers:
                        intmax += answer.priority
                        addresses[intmax] = (answer.target.to_text()[:-1],
                                             answer.port)
                    #python3 returns a generator for dictionary keys
                    priorities = [x for x in addresses.keys()]
                    priorities.sort()

                    picked = random.randint(0, intmax)
                    for priority in priorities:
                        if picked <= priority:
                            address = addresses[priority]
                            break

        if not address:
            # If all else fails, use the server from the JID.
            address = (self.boundjid.host, 5222)

        return XMLStream.connect(self, address[0], address[1], use_tls=True)

    def register_feature(self, mask, pointer, breaker=False):
        """
        Register a stream feature.

        Arguments:
            mask    -- An XML string matching the feature's element.
            pointer -- The function to execute if the feature is received.
            breaker -- Indicates if feature processing should halt with
                       this feature. Defaults to False.
        """
        self.registered_features.append((MatchXMLMask(mask),
                                         pointer,
                                         breaker))

    def update_roster(self, jid, name=None, subscription=None, groups=[]):
        """
        Add or change a roster item.

        Arguments:
            jid          -- The JID of the entry to modify.
            name         -- The user's nickname for this JID.
            subscription -- The subscription status. May be one of
                            'to', 'from', 'both', or 'none'. If set
                            to 'remove', the entry will be deleted.
            groups       -- The roster groups that contain this item.
        """
        iq = self.Iq()._set_stanza_values({'type': 'set'})
        iq['roster']['items'] = {jid: {'name': name,
                                       'subscription': subscription,
                                       'groups': groups}}
        response = iq.send()
        return response['type'] == 'result'

    def del_roster_item(self, jid):
        """
        Remove an item from the roster by setting its subscription
        status to 'remove'.

        Arguments:
            jid -- The JID of the item to remove.
        """
        return self.update_roster(jid, subscription='remove')

    def get_roster(self):
        """Request the roster from the server."""
        iq = self.Iq()._set_stanza_values({'type': 'get'}).enable('roster')
        response = iq.send()
        self._handle_roster(response, request=True)

    def _handle_stream_features(self, features):
        """
        Process the received stream features.

        Arguments:
            features -- The features stanza.
        """
        # Record all of the features.
        self.features = []
        for sub in features.xml:
            self.features.append(sub.tag)

        # Process the features.
        for sub in features.xml:
            for feature in self.registered_features:
                mask, handler, halt = feature
                if mask.match(sub):
                    if handler(sub) and halt:
                        # Don't continue if the feature was
                        # marked as a breaker.
                        return True

    def _handle_starttls(self, xml):
        """
        Handle notification that the server supports TLS.

        Arguments:
            xml -- The STARTLS proceed element.
        """
        if not self.authenticated and self.ssl_support:
            tls_ns = 'urn:ietf:params:xml:ns:xmpp-tls'
            self.add_handler("<proceed xmlns='%s' />" % tls_ns,
                             self._handle_tls_start,
                             name='TLS Proceed',
                             instream=True)
            self.sendStreamPacket(tostring(xml))
            return True
        else:
            log.warning("The module tlslite is required to log in" +\
                            " to some servers, and has not been found.")
            return False

    def _handle_tls_start(self, xml):
        """
        Handle encrypting the stream using TLS.

        Restarts the stream.
        """
        log.debug("Starting TLS")
        if self.start_tls():
            raise RestartStream()

    def _handle_sasl_auth(self, xml):
        """
        Handle authenticating using SASL.

        Arguments:
            xml -- The SASL mechanisms stanza.
        """
        if '{urn:ietf:params:xml:ns:xmpp-tls}starttls' in self.features:
            return False

        log.debug("Starting SASL Auth")
        sasl_ns = 'urn:ietf:params:xml:ns:xmpp-sasl'

        sasl_mechs = xml.findall('{%s}mechanism' % sasl_ns)
        if sasl_mechs:
            for sasl_mech in sasl_mechs:
                self.features.append("sasl:%s" % sasl_mech.text)
            if 'sasl:DIGEST-MD5' in self.features:
                self.sendStreamPacket("<auth xmlns='%s' mechanism='DIGEST-MD5'/>" %sasl_ns) 
            elif 'sasl:PLAIN' in self.features and self.boundjid.user:
                if sys.version_info < (3, 0):
                    user = bytes(self.boundjid.user)
                    password = bytes(self.password)
                else:
                    user = bytes(self.boundjid.user, 'utf-8')
                    password = bytes(self.password, 'utf-8')

                auth = base64.b64encode(b'\x00' + user + \
                                        b'\x00' + password).decode('utf-8')

                self.sendStreamPacket("<auth xmlns='%s' mechanism='PLAIN'>%s</auth>" % (
                    sasl_ns,
                    auth))
            elif 'sasl:ANONYMOUS' in self.features and not self.boundjid.user:
                self.sendStreamPacket("<auth xmlns='%s' mechanism='%s' />" % (
                    sasl_ns,
                    'ANONYMOUS'))
            else:
                log.error("No appropriate login method.")
                self.disconnect()
        return True
    
    def _handle_sasl_digest_md5_auth(self, xml):
        sasl_ns = 'urn:ietf:params:xml:ns:xmpp-sasl'
        self.add_handler("<success xmlns='%s' />" % sasl_ns,
                         self._handle_auth_success,
                         name='SASL Sucess',
                         instream=True)
        self.add_handler("<failure xmlns='%s' />" % sasl_ns,
                         self._handle_auth_fail,
                         name='SASL Failure',
                         instream=True)
        challenge = [item.split('=', 1) for item in base64.b64decode(xml.text).replace("\"", "").split(',', 6) ]
        challenge = dict(challenge)
        logging.debug("MD5 auth challenge: %s", challenge)

        if challenge.get('rspauth'): #authenticated success... send response
            self.sendStreamPacket("""<response xmlns='urn:ietf:params:xml:ns:xmpp-sasl'/>""")
            return
        #TODO: use realm if supplied by server, use default qop unless supplied by server
        #Realm, nonce, qop should all be present
        if not challenge.get('qop') or not challenge.get('nonce'):
            logging.error("Error during digest-md5 authentication. Challenge missing critical information. Challenge: %s" 
                          %base64.b64decode(xml.text))
            self._handle_auth_fail(xml)
            return
        #TODO: charset can be either UTF-8 or if not present use ISO 8859-1 defaulting for UTF-8 for now
        #Compute the cnonce - a unique hex string only used in this request
        cnonce = ""
        for i in range(7):
            cnonce+=hex(int(random.random()*65536*4096))[2:]
        cnonce = base64.encodestring(cnonce)[0:-1]
        a1 = b"%s:%s:%s" %(md5("%s:%s:%s" % (self.boundjid.user, self.boundjid.host, self.password)), 
                           challenge["nonce"].encode("UTF-8"), cnonce.encode("UTF-8") )
        a2 = "AUTHENTICATE:xmpp/%s" %self.boundjid.host
        responseHash = md5digest("%s:%s:00000001:%s:auth:%s" 
                                 %(md5digest(a1), 
                                   challenge["nonce"], 
                                   cnonce, md5digest(a2) ) )
        response = 'charset=utf-8,username="%s",realm="%s",nonce="%s",nc=00000001,cnonce="%s",digest-uri="%s",response=%s,qop=%s,' \
            % (self.boundjid.user, self.boundjid.host, challenge["nonce"], cnonce, "xmpp/%s" % self.boundjid.host, responseHash, challenge["qop"])
        self.sendStreamPacket("<response xmlns='urn:ietf:params:xml:ns:xmpp-sasl'>%s</response>" % base64.encodestring(response)[:-1])


    def _handle_auth_success(self, xml):
        """
        SASL authentication succeeded. Restart the stream.

        Arguments:
            xml -- The SASL authentication success element.
        """
        self.authenticated = True
        self.features = []
        raise RestartStream()

    def _handle_auth_fail(self, xml):
        """
        SASL authentication failed. Disconnect and shutdown.

        Arguments:
            xml -- The SASL authentication failure element.
        """
        log.info("Authentication failed.")
        self.event("failed_auth", direct=True)
        self.disconnect()

    def _handle_bind_resource(self, xml):
        """
        Handle requesting a specific resource.

        Arguments:
            xml -- The bind feature element.
        """
        log.debug("Requesting resource: %s" % self.boundjid.resource)
        xml.clear()
        iq = self.Iq(stype='set')
        if self.boundjid.resource:
            res = ET.Element('resource')
            res.text = self.boundjid.resource
            xml.append(res)
        iq.append(xml)
        response = self.sendStreamPacket(iq, True)

        bind_ns = 'urn:ietf:params:xml:ns:xmpp-bind'
        self.set_jid(response.xml.find('{%s}bind/{%s}jid' % (bind_ns,
                                                             bind_ns)).text)
        self.bound = True
        log.info("Node set to: %s" % self.boundjid.fulljid)
        session_ns = 'urn:ietf:params:xml:ns:xmpp-session'
        if "{%s}session" % session_ns not in self.features or self.bindfail:
            log.debug("Established Session")
            self.sessionstarted = True
            self.session_started_event.set()
            self.event("session_start")

    def _handle_start_session(self, xml):
        """
        Handle the start of the session.

        Arguments:
            xml -- The session feature element.
        """
        if self.authenticated and self.bound:
            iq = self.makeIqSet(xml)
            response = self.sendStreamPacket(iq, True)
            log.debug("Established Session")
            self.sessionstarted = True
            self.session_started_event.set()
            self.event("session_start")
        else:
            # Bind probably hasn't happened yet.
            self.bindfail = True

    def _handle_roster(self, iq, request=False):
        """
        Update the roster after receiving a roster stanza.

        Arguments:
            iq      -- The roster stanza.
            request -- Indicates if this stanza is a response
                       to a request for the roster.
        """
        if iq['type'] == 'set' or (iq['type'] == 'result' and request):
            for jid in iq['roster']['items']:
                if not jid in self.roster:
                    self.roster[jid] = {'groups': [],
                                        'name': '',
                                        'subscription': 'none',
                                        'presence': {},
                                        'in_roster': True}
                self.roster[jid].update(iq['roster']['items'][jid])

        self.event("roster_update", iq)
        if iq['type'] == 'set':
            iq.reply()
            iq.enable('roster')
            iq.send()
            
def md5(data):
    try:
        import hashlib
        md5 = hashlib.md5(data)
    except ImportError:
        import md5
        md5 = md5.new(data)
    return md5.digest()

def md5digest(data):
    try:
        import hashlib
        md5 = hashlib.md5(data)
    except ImportError:
        import md5
        md5 = md5.new(data)
    return md5.hexdigest()
